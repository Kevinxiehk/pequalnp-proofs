# Round 12, target 1, case (II), numerical exploration: for a random rank-3 B in the case-(II) B-space, sample the cone V_B of elements Z
# (z_3 in <1,n>, z_1 + z_2 in <1, 1_S>) with <P_0, Z> level, by Gauss-Newton from random starts (normalised), and report the dimension of the
# linear span of the solutions found (a 6-dim M needs a 3-dim linear subspace inside V_B).  Control: B of rank 2 (beta(w0) = 0).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from ext6 import F45
mode=sys.argv[1]; rg=np.random.default_rng(int(sys.argv[2]))
W=np.array([[1,-1,0,0,0],[1,0,-1,0,0],[2,0,0,-1,-1]],complex); n=np.array([0,0,0,1,-1],complex)
a=np.array([[-.5,-.5,1,0,0],[.5,-1,.5,0,0],[0,-1,1,0,0]],complex)
s=rg.normal()+1j*rg.normal(); beta=rg.normal(size=3)+1j*rg.normal(size=3)
if mode=='r2': beta[2]=(beta[0]+beta[1])/1.5          # beta(w0) = beta1 + beta2 - 1.5 beta3 = 0
U=s*a+np.outer(beta,n)
P0=[]
for i in range(3):
    E=np.zeros((4,5),complex); E[3]=W[i]; E[0]=U[i]; P0.append(E)
P0=np.array(P0)
def Zof(z):
    E=np.zeros((4,5),complex); E[3]=z[0]+z[1]*n; E[1]=z[2:7]; E[2]=z[7]+z[8]*np.array([0,0,0,1,1])-z[2:7]; E[0]=z[9:14]; return E
C=rg.normal(size=(80,4))+1j*rg.normal(size=(80,4))
def res(z):
    El=np.concatenate([P0,Zof(z)[None]],0); return np.concatenate([F45(np.einsum('nk,kij->nij',C,El))-120,[np.vdot(z,z).real-1+0j]])
sols=[]
for st in range(int(sys.argv[3])):
    z=rg.normal(size=14)+1j*rg.normal(size=14); z/=np.linalg.norm(z); rr=res(z); c=np.linalg.norm(rr)
    for it in range(80):
        J=np.empty((len(rr),14),complex)
        for k in range(14):
            zp=z.copy(); zp[k]+=1e-7; J[:,k]=(res(zp)-rr)/1e-7
        dz=np.linalg.lstsq(J,-rr,rcond=None)[0]; zn=z+dz; rn=res(zn)
        if np.linalg.norm(rn)<c: z,rr,c=zn,rn,np.linalg.norm(rn)
        else:
            zn=z+0.3*dz; rn=res(zn)
            if np.linalg.norm(rn)<c: z,rr,c=zn,rn,np.linalg.norm(rn)
            else: break
        if c<1e-11: break
    if c<1e-9: sols.append(z)
print(mode,'solutions found:',len(sols),'of',sys.argv[3])
if sols:
    S=np.array(sols); sv=np.linalg.svd(S,compute_uv=False); print('  singular values of the solution matrix:',np.round(sv/sv[0],6)[:8])
    print('  dim of linear span of V_B samples:',int((sv>1e-6*sv[0]).sum()))
