# (NCOL) direct test: 4x5 level spaces of dim d whose defect space lies in a FIXED generic e-dim subspace C0 of 1^perp
# (generic C0 has no neutral column).  usage: d e s0 s1 tmax [neutral]   (neutral=1: C0 generic inside e_0^perp, as a control)
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time
from clm import *
class PF(Problem):
    def __init__(self,d,e,seed,neutral=False):
        Problem.__init__(self,4,d,'defect',e,seed=seed)
        rng=np.random.default_rng(1000+seed)
        if neutral is True:   # choose Fb so that the first 3 rows span 1^perp cap e_0^perp, and C0 = span of e generic vectors of it
            B=rng.normal(size=(3,5))+1j*rng.normal(size=(3,5)); B[:,0]=0; B=B-0; B[:,1:]-=B[:,1:].mean(1)[:,None]
            f4=np.array([4,-1,-1,-1,-1.])/np.sqrt(20); q,_=np.linalg.qr(np.concatenate([B,f4[None]],0).T)
            self.Fb=q.T; self.Fd=q.conj().T
            T=np.zeros((e,4-e),complex)
            if e<3: T[:,:3-e]=rng.normal(size=(e,3-e))+1j*rng.normal(size=(e,3-e))
            self.T0=T
        elif neutral=='b32':   # C0 = V_{012} + V_{34}  (block pattern (3,2), no neutral column); e must be 3
            B=np.array([[1,-1,0,0,0],[1,1,-2,0,0],[0,0,0,1,-1]],complex); f4=np.array([2,2,2,-3,-3.])
            q,_=np.linalg.qr(np.concatenate([B,f4[None]],0).T); self.Fb=q.T; self.Fd=q.conj().T; self.T0=np.zeros((e,4-e),complex)
        else: self.T0=rng.normal(size=(e,4-e))+1j*rng.normal(size=(e,4-e))
        self.nvar=self.nW
    def fun(self,z,jac=True):
        zz=np.concatenate([z,self.T0.ravel()])
        if not jac: return Problem.fun(self,zz,False)
        r,J=Problem.fun(self,zz,True); return r,J[:,:self.nW]
    def C0(self): return np.concatenate([np.eye(self.e),self.T0],1)@self.Fb
d,e,s0,s1=[int(a) for a in sys.argv[1:5]]; tmax=float(sys.argv[5]); neutral=(True if sys.argv[6]=='1' else sys.argv[6]) if len(sys.argv)>6 else False
t0=time.time(); nf=0; ntry=0; res=[]
for s in range(s0,s1):
    if time.time()-t0>tmax: break
    P=PF(d,e,s,neutral); z,c=solve(P,iters=250); ntry+=1; res.append(c)
    Z=P.basis(z); cond=np.linalg.cond(Z.reshape(d,-1))
    if c<1e-9 and cond<1e6:
        nf+=1; sv=defect_dim(Z)
        print('d=%d e=%d seed %d res %.1e cond %.1e defect sv %s  min|C0 entries| %.2f'%(d,e,s,c,cond,np.array2string(sv[:5],precision=2),np.abs(P.C0()).max(0).min()),flush=True)
print('(fixC%s) d=%d, defect inside fixed generic %d-dim C0: found %d of %d; smallest residuals %s; t=%.0f'%((' with neutral column' if neutral is True else ' '+str(neutral)) if neutral else '',d,e,nf,ntry,np.array2string(np.sort(res)[:4],precision=2),time.time()-t0))
