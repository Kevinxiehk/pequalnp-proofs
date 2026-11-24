# Exact data for the KERNEL LEMMA on a ruling (cached v4 setup): B := B1 + 2 B2 + 3 B3; r = generic rank (= nq - 1 expected);
# locus where rank B < r (gcd of r x r compressions); kernel vector k of B over Q(params); q0(k,k) (factored).
import sys, pickle, random, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
F=sp.QQ.frac_field(*par); R=sp.QQ[tuple(par)]
DM=lambda M,dom: DomainMatrix.from_Matrix(M).convert_to(dom)
B=Gs[1]+2*Gs[2]+3*Gs[3]; r=DM(B,F).rank(); print('nq',nq,' generic rank of B:',r,flush=True)
random.seed(5); g=0
for _ in range(3):
    U=sp.Matrix(r,nq,lambda i,j: random.randint(-3,3)); V=sp.Matrix(nq,r,lambda i,j: random.randint(-3,3))
    d=sp.factor(DM(U*B*V,R).det().as_expr()); g=sp.gcd(g,d) if g!=0 else d
print('rank B < %d only on zeros of:'%r,sp.factor(g),flush=True)
k=DM(B,F).nullspace().to_Matrix().applyfunc(sp.cancel)
k=k*sp.lcm([sp.fraction(sp.together(e))[1] for e in k]); k=k.applyfunc(lambda e: sp.factor(sp.cancel(e)))
print('kernel dim',k.rows,flush=True)
qk=sp.factor((k*Gs[0]*k.T)[0,0]); print('q0(k,k) =',qk,flush=True)
print('complement determinant:',detX,' denominators:',[sp.factor(d) for d in dens],flush=True)
