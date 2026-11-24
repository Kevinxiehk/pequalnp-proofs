# Rank structure of the forms on a cached F2col setup: individual B_z, pairs, generic combination, q0; kernels and their intersections (exact over Q(params)).
import sys, pickle, itertools, sympy as sp
from sympy.polys.matrices import DomainMatrix
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(sys.argv[1],'rb'))
F=sp.QQ.frac_field(*par); DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
print('params',par,'nq',nq,'detX',sp.factor(detX),'rkjump',rkjump,'dens',[sp.factor(d) for d in dens],flush=True)
for z in range(1,len(Gs)): print('rank B_%d ='%z,DM(Gs[z]).rank(),flush=True)
for z,w in itertools.combinations(range(1,len(Gs)),2): print('rank stack(B_%d,B_%d) ='%(z,w),DM(sp.Matrix.vstack(Gs[z],Gs[w])).rank(),flush=True)
print('rank q0 =',DM(Gs[0]).rank(),flush=True)
for z in range(1,len(Gs)):
    K=DM(Gs[z]).nullspace().to_Matrix(); print('ker B_%d dim %d; rank of q0 on ker B_%d = %d'%(z,K.rows,z,DM(K*Gs[0]*K.T).rank()),flush=True)
    for w in range(1,len(Gs)):
        if w!=z: print('   rank of B_%d on ker B_%d = %d'%(w,z,DM(K*Gs[w]*K.T).rank()),flush=True)
