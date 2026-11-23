"""5x5 level spaces containing a split free row pair  T = e_4 (x) U (+) e_5 (x) U'  (dim U = k, dim U' = 4-k, unknown),
   plus dpp further vectors whose 3-row parts (rows 0..2) are independent.  Level dim = 4 + dpp.
   Holomorphic LM; all unknowns enter X linearly."""
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time
from clm import *
class Split:
    def __init__(self,k,dpp,seed=0,N=220):
        self.k,self.kp,self.dpp=k,4-k,dpp; rng=np.random.default_rng(seed); self.rng=rng; self.N=N
        def chart(m):
            # affine chart of Gr(m,5): u_a = base_a + sum_c t_ac n_c, with Lam u_a = e_a
            if m==0: return np.zeros((0,5),complex),np.zeros((0,5),complex)
            Lam=rng.normal(size=(m,5))+1j*rng.normal(size=(m,5)); base=np.linalg.pinv(Lam)[:, :m].T  # (m,5): Lam base_a = e_a
            u,s,vh=np.linalg.svd(Lam); nul=vh[m:].conj()                                              # (5-m,5): Lam n = 0
            return base,nul
        self.bU,self.nU=chart(self.k); self.bV,self.nV=chart(self.kp)
        M=rng.normal(size=(15,15))+1j*rng.normal(size=(15,15)); self.Pi,_=np.linalg.qr(M)
        self.nt1=self.k*(5-self.k); self.nt2=self.kp*(5-self.kp); self.nv=dpp*(15-dpp); self.nr=dpp*10
        self.nvar=self.nt1+self.nt2+self.nv+self.nr
        nc=4+dpp; A=rng.normal(size=(N,nc))+1j*rng.normal(size=(N,nc)); self.A=A/np.linalg.norm(A,axis=1)[:,None]
        self.R=Rlevel(5)
        # constant derivative tensor T[n,u,25] and constant part X0[n,25]
        T=np.zeros((N,self.nvar,25),complex); X0=np.zeros((N,25),complex); A=self.A; o=0
        for a in range(self.k):
            X0[:,15:20]+=A[:,a][:,None]*self.bU[a][None,:]
            for c in range(5-self.k):
                T[:,o,15:20]=A[:,a][:,None]*self.nU[c][None,:]; o+=1
        for b in range(self.kp):
            X0[:,20:25]+=A[:,self.k+b][:,None]*self.bV[b][None,:]
            for c in range(5-self.kp):
                T[:,o,20:25]=A[:,self.k+b][:,None]*self.nV[c][None,:]; o+=1
        for l in range(dpp):
            X0[:,:15]+=A[:,4+l][:,None]*self.Pi[l][None,:]
            for c in range(15-dpp):
                T[:,o,:15]=A[:,4+l][:,None]*self.Pi[dpp+c][None,:]; o+=1
        for l in range(dpp):
            for c in range(10):
                T[:,o,15+c]=A[:,4+l]; o+=1
        self.T=T; self.X0=X0
    def fun(self,z,jac=True):
        X=(self.X0+np.einsum('nuc,u->nc',self.T,z)).reshape(self.N,5,5)
        G,loo=G_and_loo(X); r=G@self.R.T
        if not jac: return r.ravel()
        dG=np.stack([np.stack([shiftj(loo[i],j) for j in range(Q)],1) for i in range(5)],1)        # (N,5,5,32)
        D=np.einsum('nijs,rs->nrij',dG,self.R).reshape(self.N,-1,25)
        J=np.einsum('nrc,nuc->nru',D,self.T).reshape(self.N*5,self.nvar)
        return r.ravel(),J
    def basis(self,z):
        o=0; B=[]
        tU=z[o:o+self.nt1].reshape(self.k,5-self.k); o+=self.nt1; tV=z[o:o+self.nt2].reshape(self.kp,5-self.kp); o+=self.nt2
        V=z[o:o+self.nv].reshape(self.dpp,15-self.dpp); o+=self.nv; Rr=z[o:].reshape(self.dpp,10)
        for a in range(self.k):
            M=np.zeros((5,5),complex); M[3]=self.bU[a]+tU[a]@self.nU; B.append(M)
        for b in range(self.kp):
            M=np.zeros((5,5),complex); M[4]=self.bV[b]+tV[b]@self.nV; B.append(M)
        F3=np.concatenate([np.eye(self.dpp),V],1)@self.Pi
        for l in range(self.dpp):
            M=np.zeros((5,5),complex); M[:3]=F3[l].reshape(3,5); M[3:]=Rr[l].reshape(2,5); B.append(M)
        return np.array(B)
if __name__=='__main__':
    k=int(sys.argv[1]); dpp=int(sys.argv[2]); ns=int(sys.argv[3]); tmax=float(sys.argv[4]); t0=time.time(); res=[]; nf=0
    for s in range(ns):
        if time.time()-t0>tmax: break
        P=Split(k,dpp,seed=s); z,c=solve(P,iters=250); B=P.basis(z); cond=np.linalg.cond(B.reshape(len(B),-1)); res.append(c if cond<1e7 else 9e9)
        if c<1e-9 and cond<1e7: nf+=1; np.save('split_k%d_d%d_s%d.npy'%(k,dpp,s),B)
    print('split pair (dim U, dim U\') = (%d,%d), %d more vectors -> level dim %d: found %d of %d; smallest res %s; t=%.0f'%(k,4-k,dpp,4+dpp,nf,len(res),np.array2string(np.sort(res)[:4],precision=1),time.time()-t0),flush=True)
