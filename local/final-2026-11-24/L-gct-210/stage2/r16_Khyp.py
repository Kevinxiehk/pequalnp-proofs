# Exact check of the K-reduction hypotheses on a whole F2col ruling (from the cached v4 setup): over the function field Q(params):
#   rank q0 = 8 ? ; rank of the stacked B-forms (common kernel dim) ; rank of a fixed combination B1 + 2 B2 + 3 B3 (should be 6) ;
#   q0 restricted to K (2x2) not identically zero ; degeneracy polynomials via gcds of random integer compressions.
import sys, pickle, random, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
print('parameters',par,' nq',nq,' forms',len(Gs),flush=True)
F=sp.QQ.frac_field(*par); R=sp.QQ[tuple(par)]
def DM(M,dom): return DomainMatrix.from_Matrix(M).convert_to(dom)
G0,G1,G2,G3=Gs[0],Gs[1],Gs[2],Gs[3]
print('rank q0 over Q(params):',DM(G0,F).rank(),flush=True)
d0=sp.factor(DM(G0,R).det().as_expr()); print('det q0 =',d0,flush=True)
Bst=sp.Matrix.vstack(G1,G2,G3); rB=DM(Bst,F).rank(); print('rank of stacked B-forms:',rB,' -> common kernel dim',nq-rB,flush=True)
Gc=G1+2*G2+3*G3; print('rank of B1+2B2+3B3:',DM(Gc,F).rank(),flush=True)
# common kernel basis over Q(params)
Kb=DM(Bst,F).nullspace().to_Matrix()
Kb=Kb.applyfunc(sp.cancel)
print('K basis (rows):',Kb.shape,flush=True)
QK=(Kb*G0*Kb.T).applyfunc(sp.factor)
print('q0 on K (2x2):',QK,flush=True)
print('q0|K identically zero?', all(sp.simplify(e)==0 for e in QK),flush=True)
# degeneracy: gcd of random 6x6 compressions of the combination (where rank < 6) and of 6x6 compressions of the stack (where kernel jumps)
random.seed(4)
def rnd(r,c): return sp.Matrix(r,c,lambda i,j: random.randint(-3,3))
g=0
for _ in range(3):
    d=sp.factor(DM(rnd(6,nq)*Gc*rnd(nq,6),R).det().as_expr()); g=sp.gcd(g,d) if g!=0 else d
print('combination rank < 6 only on zeros of:',sp.factor(g),flush=True)
g=0
for _ in range(3):
    d=sp.factor(DM(rnd(6,3*nq)*Bst*rnd(nq,6),R).det().as_expr()); g=sp.gcd(g,d) if g!=0 else d
print('B-stack rank < 6 (kernel > 2) only on zeros of:',sp.factor(g),flush=True)
