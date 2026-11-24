# Rank structure of the forms on a cached (1-parameter) family and the GENERAL KERNEL BOUND [NOTES-stage2 R18-1]:
#   B_c (generic c) has rank r and kernel W; a 4-dim common isotropic L'' meets W in dim >= m := 4 - floor(r/2). If W = K (common kernel of all B_z),
#   L'' cap K is q0-isotropic, so m <= (dim K - rho) + floor(rho/2), rho = rank q0|K.  Violated -> KILLED (generically on the family).
import sys, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(sys.argv[1],'rb'))
F=sp.QQ.frac_field(*par) if par else sp.QQ; DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
Bst=sp.Matrix.vstack(*Gs[1:]); rs=DM(Bst).rank(); kap=nq-rs
out={}
for c in [(1,2,3),(2,-1,5),(3,1,-2)]:
    B=sum((ci*G for ci,G in zip(c,Gs[1:])),sp.zeros(nq,nq)); out[c]=DM(B).rank()
r=max(out.values())
K=DM(Bst).nullspace().to_Matrix().applyfunc(sp.cancel) if kap>0 else sp.zeros(0,nq)
rho=DM(K*Gs[0]*K.T).rank() if kap>0 else 0
m=4-r//2; maxiso=(kap-rho)+rho//2
print('fix',fix,'nq',nq,'| ranks B_z',[DM(G).rank() for G in Gs[1:]],'| B-stack',rs,'(dim K =',kap,') | generic B_c rank',r,'| ker B_c = K:',nq-r==kap,
      '| rank q0|K',rho,'| need dim(L cap ker) >=',m,'| max q0-isotropic in K',maxiso,flush=True)
if nq-r==kap and maxiso<m: print('  => KILLED generically by the general kernel bound',flush=True)
elif nq-r==kap: print('  => reduction: L\'\' contains an %d-dim q0-isotropic subspace of K (dim %d, rank %d)'%(m,kap,rho),flush=True)
else: print('  => ker B_c strictly bigger than K: use the B_w restricted to ker B_c',flush=True)
if kap>0: print('  q0|K =',(K*Gs[0]*K.T).applyfunc(sp.factor).tolist(),flush=True)
