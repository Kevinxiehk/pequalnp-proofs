"""Sanity check of Theorem FL2* for dim U = 1: FIXED m; level spaces containing T = e_3 m^T (+) e_4 (x) {1,m}^perp with dpp extra
   vectors (independent 3-row parts).  Theorem: m.m != 0 and at most one zero entry  =>  dim <= 7 (dpp <= 3)."""
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time
from clm import *
from splitpair import Split
class SplitFixedU(Split):
    def __init__(self,U,V,dpp,seed=0,N=200):
        self.k,self.kp,self.dpp=len(U),len(V),dpp; rng=np.random.default_rng(seed); self.rng=rng; self.N=N
        self.bU,self.nU=U,np.zeros((0,5),complex); self.bV,self.nV=V,np.zeros((0,5),complex)
        M=rng.normal(size=(15,15))+1j*rng.normal(size=(15,15)); self.Pi,_=np.linalg.qr(M)
        self.nt1=0; self.nt2=0; self.nv=dpp*(15-dpp); self.nr=dpp*10; self.nvar=self.nv+self.nr
        nc=4+dpp; A=rng.normal(size=(N,nc))+1j*rng.normal(size=(N,nc)); self.A=A/np.linalg.norm(A,axis=1)[:,None]; self.R=Rlevel(5)
        T=np.zeros((N,self.nvar,25),complex); X0=np.zeros((N,25),complex); A=self.A; o=0
        for a in range(self.k): X0[:,15:20]+=A[:,a][:,None]*U[a][None,:]
        for b in range(self.kp): X0[:,20:25]+=A[:,self.k+b][:,None]*V[b][None,:]
        for l in range(dpp):
            X0[:,:15]+=A[:,4+l][:,None]*self.Pi[l][None,:]
            for c in range(15-dpp):
                T[:,o,:15]=A[:,4+l][:,None]*self.Pi[dpp+c][None,:]; o+=1
        for l in range(dpp):
            for c in range(10):
                T[:,o,15+c]=A[:,4+l]; o+=1
        self.T=T; self.X0=X0
def run(m,label,cases,tmax=40):
    m=np.array(m,complex); U=m[None,:]/np.linalg.norm(m); V=np.linalg.svd(np.concatenate([U,np.ones((1,5))]))[2][2:].conj()
    for dpp,ns in cases:
        t0=time.time(); res=[]
        for s in range(ns):
            if time.time()-t0>tmax: break
            P=SplitFixedU(U,V,dpp,seed=s); z,c=solve(P,iters=250); res.append(c)
        print('%s: %d extra vectors (dim %d): %d of %d below 1e-9; smallest residuals %s'%(label,dpp,4+dpp,sum(r<1e-9 for r in res),len(res),np.array2string(np.sort(res)[:3],precision=1)),flush=True)
run([1,2,-4,1,0],'m=(1,2,-4,1,0) [one zero, non-isotropic]',((3,6),(4,8)))
run([3,1,-2,5,-7],'m=(3,1,-2,5,-7) [no zero, non-isotropic]',((2,5),(3,6),(4,6)),tmax=30)
