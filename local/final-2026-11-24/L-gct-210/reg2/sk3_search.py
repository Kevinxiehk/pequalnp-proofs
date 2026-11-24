# Round 10, target 3.  After SK2 => [diag(zeta), K] = 0 (K = 5x5 skew extension of B, K 1 = 0), rank B <= 2 unless EVERY Z in M has constant
# zeta_Z = z_k + z_l.  Then (1,1) forces z_j constant; with z_r normalised constant: Z = a e_r 1 + b e_j 1 + e_k p + e_l (lam 1 - p).
# Numerical search (Gauss-Newton) for 6-dim level spaces  P (+) <Z1,Z2>,  P = {e_r w + e_j K w : w in 1^perp},  with Pf-normalisation phi = 1
# (rank K = 4).  rows: r = 3, j = 0, k = 1, l = 2.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from ext6 import F45
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
iu=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def Kmat(k):
    K=np.zeros((5,5),complex)
    for v,(a,b) in zip(k,iu): K[a,b]=v; K[b,a]=-v
    K[:4,4]=-K[:4,:4].sum(1); K[4,:4]=-K[:4,4]      # K 1 = 0
    return K
def pf4(K): return K[0,1]*K[2,3]-K[0,2]*K[1,3]+K[0,3]*K[1,2]
def build(x):
    K=Kmat(x[:6]); El=[]
    for m in range(4):
        wv=np.zeros(5); wv[m]=1; wv[4]=-1; E=np.zeros((4,5),complex); E[3]=wv; E[0]=K@wv; El.append(E)
    for i in range(2):
        a,b,p=x[6+7*i],x[7+7*i],x[8+7*i:13+7*i]; lam=-a-b
        Z=np.zeros((4,5),complex); Z[3]=a; Z[0]=b; Z[1]=p; Z[2]=lam-p; El.append(Z)
    return K,np.array(El)
C=rg.normal(size=(150,6))+1j*rg.normal(size=(150,6))
nrm=rg.normal(size=(2,7))+1j*rg.normal(size=(2,7))
def res(x):
    K,El=build(x); r=F45(np.einsum('nk,kij->nij',C,El))-120
    # normalisations: Pf = 1 (rank 4), Z1, Z2 not degenerate: two random affine normalisations of the Z data
    z1=nrm@x[6:13]; z2=nrm@x[13:20]   # generic GL2 normalisation of <Z1,Z2>
    return np.concatenate([r,[pf4(K)-1,z1[0]-1,z1[1],z2[0],z2[1]-1]])
hits=0; ranks=[]
for start in range(int(sys.argv[2]) if len(sys.argv)>2 else 20):
    x=rg.normal(size=20)+1j*rg.normal(size=20); rr=res(x); c=np.linalg.norm(rr)
    for it in range(150):
        J=np.empty((len(rr),20),complex)
        for a in range(20):
            xp=x.copy(); xp[a]+=1e-7; J[:,a]=(res(xp)-rr)/1e-7
        dx=np.linalg.lstsq(J,-rr,rcond=None)[0]; lam=1.0
        while lam>1e-4:
            xn=x+lam*dx; rn=res(xn)
            if np.linalg.norm(rn)<c: x,rr,c=xn,rn,np.linalg.norm(rn); break
            lam/=2
        else: break
        if c<1e-10: break
    K,El=build(x)
    dimM=np.linalg.matrix_rank(El.reshape(6,20),tol=1e-6)
    print('start %d: residual %.1e  rank K = %d  dim M = %d'%(start,c,np.linalg.matrix_rank(K,tol=1e-6),dimM),flush=True)
    if c<1e-8 and dimM==6: hits+=1
print('converged 6-dim level solutions with Pf(K) = 1:',hits)
