# (NC') search: 4x5 level spaces of dim d, defect space of dim <= e (unknown), with neutral columns 0..k-1.  usage: d e k s0 s1 tmax
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, time
from clm import *
class PN(Problem):
    def __init__(self,d,e,k,seed):
        Problem.__init__(self,4,d,'defect',e,seed=seed); self.k=k
    def fun(self,z,jac=True):
        N,d=self.N,self.d; n=4*Q
        Zf=self.Zfull(z); X=(self.A@Zf).reshape(N,4,Q); G,loo=G_and_loo(X)
        rx=np.einsum('ns,kjs->nkj',G,self.Rd)[:,:,:self.k].reshape(-1)
        if not jac: return np.concatenate([Problem.fun(self,z,False),rx])
        r,J=Problem.fun(self,z,True)
        dG=np.stack([np.stack([shiftj(loo[i],j) for j in range(Q)],1) for i in range(4)],1)
        dpk=np.einsum('nijs,kms->nkmij',dG,self.Rd[:,:self.k,:]).reshape(N,4*self.k,n)
        DP=dpk@self.Pi[d:].T
        JW=np.einsum('na,nrb->nrab',self.A,DP).reshape(N*4*self.k,self.nW)
        Jx=np.concatenate([JW,np.zeros((JW.shape[0],self.nvar-self.nW),complex)],1)
        return np.concatenate([r,rx]),np.concatenate([J,Jx],0)
d,e,k,s0,s1=[int(a) for a in sys.argv[1:6]]; tmax=float(sys.argv[6])
t0=time.time(); nf=0; ntry=0; res=[]
for s in range(s0,s1):
    if time.time()-t0>tmax: break
    P=PN(d,e,k,s); z,c=solve(P,iters=250); ntry+=1; res.append(c)
    Z=P.basis(z); cond=np.linalg.cond(Z.reshape(d,-1))
    if c<1e-9 and cond<1e6:
        nf+=1; sv=defect_dim(Z)
        print('d=%d e=%d k=%d seed %d res %.1e cond %.1e defect sv %s'%(d,e,k,s,c,cond,np.array2string(sv[:5],precision=2)),flush=True)
        np.save('ncdef_d%d_e%d_k%d_s%d.npy'%(d,e,k,s),Z)
print("(NC') d=%d e<=%d k=%d: found %d of %d; smallest residuals %s; t=%.0f"%(d,e,k,nf,ntry,np.array2string(np.sort(res)[:4],precision=2),time.time()-t0))
