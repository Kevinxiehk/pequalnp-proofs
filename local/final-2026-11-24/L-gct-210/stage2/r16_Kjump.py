# Jump locus (nq = 10): rank B_z = 7, so a 4-dim common isotropic L'' meets every ker B_z (dim 3) [4 - floor(7/2) = 1]. On W_z = ker B_z the other
# B_w have rank 1 (B_w|W = l_w^2), so k in L'' cap W_z satisfies l_w(k) = 0 for both w != z: if these two linear forms are independent on W_z, k spans
# W_z cap {l_w = 0} = C k0 (k0 = common kernel of all B), and q0(k0,k0) = 0 is forced.  Exact data over Q(params) [NOTES-stage2 R15-6].
import sys, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(sys.argv[1],'rb'))
F=sp.QQ.frac_field(*par); R=sp.QQ[tuple(par)]; DM=lambda M,d=F: DomainMatrix.from_Matrix(M).convert_to(d)
k0=DM(sp.Matrix.vstack(*Gs[1:])).nullspace().to_Matrix().row(0).applyfunc(sp.cancel)
print('k0 =',[sp.factor(x) for x in k0],flush=True)
print('q0(k0,k0) =',sp.factor(sp.cancel((k0*Gs[0]*k0.T)[0,0])),flush=True)
for z in (1,2,3):
    W=DM(Gs[z]).nullspace().to_Matrix().applyfunc(sp.cancel)
    others=[w for w in (1,2,3) if w!=z]
    St=sp.Matrix.vstack(*[(W*Gs[w]*W.T).applyfunc(sp.cancel) for w in others])
    print('z=%d: rank of [B_w|W ; B_w''|W] = %d (2 => l_w, l_w'' independent on W_z)'%(z,DM(St).rank()),flush=True)
# degeneracy certificates in 2 parameters: principal 7-minors of B_1 not containing a fixed index pattern, gcd
import random; random.seed(7)
for z in (1,2,3):
    g=0
    for _ in range(3):
        U=sp.Matrix(7,nq,lambda i,j: random.randint(-3,3)); d=sp.factor(DM(U*Gs[z]*U.T,R).det().as_expr()); g=sp.gcd(g,d) if g!=0 else d
    print('rank B_%d < 7 only on V(d1,d2,d3); gcd ='%z,sp.factor(g),flush=True)
