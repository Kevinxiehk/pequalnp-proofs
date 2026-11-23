"""Level spaces inside the class of 5x5 matrices with EQUAL ROWS in blocks (multiplicity pattern mu):
   F_mu(l_1..l_k) = int prod (sigma + l_i)^{mu_i} = 120.  Total 5x5 level dim = dim L_mu + (5 - k) (block-internal
   single-column sum-zero parts).  Holomorphic LM on Grassmannian chart of the k*5-dim ambient space."""
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time
from clm import *
class MultProblem(Problem):
    def __init__(self,mu,d,seed=0,N=None):
        self.mu=mu; k=len(mu); self.k=k
        self.p,self.d,self.mode,self.e=5,d,'level',0
        rng=np.random.default_rng(seed); self.rng=rng
        n=k*Q; self.namb=n
        Emb=np.zeros((n,25))
        r=0
        for b,m in enumerate(mu):
            for _ in range(m):
                for j in range(Q): Emb[b*Q+j,r*Q+j]=1
                r+=1
        self.Emb=Emb
        M=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)); q,_=np.linalg.qr(M); self.Pi=q@Emb     # (n,25)
        self.N=N or 160
        A=rng.normal(size=(self.N,d))+1j*rng.normal(size=(self.N,d)); self.A=A/np.linalg.norm(A,axis=1)[:,None]
        self.nW=d*(n-d); self.R=Rlevel(5); self.nvar=self.nW
if __name__=='__main__':
    mu=tuple(int(c) for c in sys.argv[1]); d=int(sys.argv[2]); ns=int(sys.argv[3]); tmax=float(sys.argv[4])
    t0=time.time(); nf=0; res=[]; nt=0
    for s in range(ns):
        if time.time()-t0>tmax: break
        P=MultProblem(mu,d,seed=s); z,c=solve(P,iters=300); Z=P.basis(z); cond=np.linalg.cond(Z.reshape(d,-1)); nt+=1; res.append(c)
        if c<1e-10 and cond<1e6:
            nf+=1; np.save('mult_%s_d%d_s%d.npy'%(sys.argv[1],d,s),Z)
    print('mu=%s d=%d (5x5 dim would be %d): found %d of %d; smallest res %s; t=%.0f'%(sys.argv[1],d,d+5-len(mu),nf,nt,np.array2string(np.sort(res)[:4],precision=1),time.time()-t0),flush=True)
