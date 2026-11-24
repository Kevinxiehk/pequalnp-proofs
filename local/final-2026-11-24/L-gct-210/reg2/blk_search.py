# Round 9, target 3 (evidence): search for 6-dim 4x5 level spaces containing a NON-SKEW two-column element E = x e_0^T + y e_1^T with sum x = 1
# (MODE 'nonskew'), resp. a 4-dim two-row block {e_0 w^T + e_1 (B w)^T : w in W} (MODE 'row4', W = 4-dim, B arbitrary).  Holomorphic
# Gauss-Newton in random charts; calibration MODE 'skew' (sum x = 0 two-column element, which must be found -- lines or skew blocks).
# usage: blk_search.py MODE SEED NSTARTS
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from ext6 import F45
from t import rank, null, level_err
from a5 import onb
mode,seed,ns=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]); rg=np.random.default_rng(seed)
H20=null(np.ones((1,20)))            # sum-zero 4x5 matrices (19-dim)
if mode in ('nonskew','skew'):
    nfix=8; drest=5
else:
    nfix=4*5+4*5; drest=2          # W basis (4 vectors in C^5) and B w images (4 vectors in C^5); rest 2-dim
def build(z,Q):
    if mode in ('nonskew','skew'):
        x=z[:4]; y=z[4:8]; E=np.zeros((4,5),complex); E[:,0]=x; E[:,1]=y; first=[E]
    else:
        W=z[:20].reshape(4,5); BW=z[20:40].reshape(4,5); first=[]
        for k in range(4):
            E=np.zeros((4,5),complex); E[0]=W[k]; E[1]=BW[k]; first.append(E)
    zr=z[nfix:].reshape(drest,19-drest); Rc=np.concatenate([np.eye(drest),zr],1)@Q
    rest=list((Rc@H20).reshape(drest,4,5))
    return np.array(first+rest)
def solve(iters=80):
    nz=nfix+drest*(19-drest); N=3*nz+30
    Q=np.linalg.qr(rg.normal(size=(19,19))+1j*rg.normal(size=(19,19)))[0]
    C=rg.normal(size=(N,6))+1j*rg.normal(size=(N,6))
    def res(z):
        B=build(z,Q); r=F45(np.einsum('nk,kij->nij',C,B))-120
        if mode=='nonskew': r=np.concatenate([r,[10*(z[:4].sum()-1)]])
        if mode=='skew': r=np.concatenate([r,[10*z[:4].sum(),10*(np.vdot(z[:4],z[:4]).real-1)]])
        return r
    z=(rg.normal(size=nz)+1j*rg.normal(size=nz))*0.4; r=res(z); c=np.linalg.norm(r); lam=1e-3
    for it in range(iters):
        h=1e-7; J=np.empty((len(r),nz),complex)
        for a in range(nz):
            zp=z.copy(); zp[a]+=h; J[:,a]=(res(zp)-r)/h
        A=J.conj().T@J; g=J.conj().T@r; ok=False
        for _ in range(6):
            dz=np.linalg.solve(A+lam*np.eye(nz)*max(1,np.abs(np.diag(A)).max()*1e-6),-g); zn=z+dz; rn=res(zn); cn=np.linalg.norm(rn)
            if cn<c: z,r,c=zn,rn,cn; lam=max(lam/4,1e-12); ok=True; break
            lam*=8
        if not ok or c<1e-11: break
    return c,build(z,Q)
hits=0
for s in range(ns):
    c,B=solve()
    if c<1e-9:
        Bo=onb(B)
        if len(Bo)==6 and level_err(Bo,ntest=20)<1e-8:
            hits+=1; print('%s start %d: 6-dim level space found (residual %.1e)'%(mode,s,c),flush=True)
            np.save('/home/kevxhk/work/L-gct-210/reg2/blk_%s_%d_%d.npy'%(mode,seed,s),Bo)
print('%s: %d hits in %d starts'%(mode,hits,ns))
