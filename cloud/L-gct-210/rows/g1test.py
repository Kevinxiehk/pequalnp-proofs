"""Test (G_1): M = 2x5 level space with BOTH row sums zero; T(M) = defect space. Claim dim M <= dim T(M)."""
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time
from clm import *
class P0(Problem):
    def fun(self,z,jac=True):
        p,d,N=self.p,self.d,self.N; n=p*Q
        Zf=self.Zfull(z); X=(self.A@Zf).reshape(N,p,Q); r2=X.sum(2)        # (N,p) row sums
        if not jac:
            return np.concatenate([Problem.fun(self,z,False),r2.ravel()])
        r,J=Problem.fun(self,z,True)
        S=np.zeros((p,n)); 
        for i in range(p): S[i,i*Q:(i+1)*Q]=1
        SP=S@self.Pi[d:].T                         # (p,n-d)
        JW=np.einsum('na,ib->niab',self.A,SP).reshape(N*p,self.nW)
        J2=np.concatenate([JW,np.zeros((N*p,self.nvar-self.nW),complex)],1)
        return np.concatenate([r,r2.ravel()]),np.concatenate([J,J2],0)
def run(p,d,e,ns,tmax):
    t0=time.time(); nf=0; nt=0; res=[]
    for s in range(ns):
        if time.time()-t0>tmax: break
        P=P0(p,d,'defect',e,seed=s); z,c=solve(P,iters=300); Z=P.basis(z); cond=np.linalg.cond(Z.reshape(d,-1)); nt+=1; res.append(c if cond<1e6 else 9e9)
        if c<1e-9 and cond<1e6: nf+=1; np.save('g1_p%d_d%d_e%d_s%d.npy'%(p,d,e,s),Z)
    print('%dx5, row sums 0, (dim M, dim T)=(%d,%d): found %d of %d; smallest res %s'%(p,d,e,nf,nt,np.array2string(np.sort(res)[:3],precision=1)),flush=True)
if __name__=='__main__':
    for (d,e) in [(1,1),(2,2),(3,3),(2,1),(3,2),(4,3),(4,4)]: run(2,d,e,14,6)
