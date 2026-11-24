"""Sanity check of Theorem FL2-gen: FIXED generic 2-dim U in 1^perp, U' = (U + C1)^perp; level spaces containing T_U."""
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, time, itertools
from clm import *
from splitpair import Split
from lib import perm
class SplitFixed(Split):
    def __init__(self,U,V,dpp,seed=0,N=200):
        self.k,self.kp,self.dpp=2,2,dpp; rng=np.random.default_rng(seed); self.rng=rng; self.N=N
        self.bU,self.nU=U,np.zeros((0,5),complex); self.bV,self.nV=V,np.zeros((0,5),complex)
        M=rng.normal(size=(15,15))+1j*rng.normal(size=(15,15)); self.Pi,_=np.linalg.qr(M)
        self.nt1=0; self.nt2=0; self.nv=dpp*(15-dpp); self.nr=dpp*10; self.nvar=self.nv+self.nr
        nc=4+dpp; A=rng.normal(size=(N,nc))+1j*rng.normal(size=(N,nc)); self.A=A/np.linalg.norm(A,axis=1)[:,None]; self.R=Rlevel(5)
        T=np.zeros((N,self.nvar,25),complex); X0=np.zeros((N,25),complex); A=self.A; o=0
        for a in range(2): X0[:,15:20]+=A[:,a][:,None]*U[a][None,:]
        for b in range(2): X0[:,20:25]+=A[:,2+b][:,None]*V[b][None,:]
        for l in range(dpp):
            X0[:,:15]+=A[:,4+l][:,None]*self.Pi[l][None,:]
            for c in range(15-dpp):
                T[:,o,:15]=A[:,4+l][:,None]*self.Pi[dpp+c][None,:]; o+=1
        for l in range(dpp):
            for c in range(10):
                T[:,o,15+c]=A[:,4+l]; o+=1
        self.T=T; self.X0=X0
    def basis(self,z):
        V=z[:self.nv].reshape(self.dpp,15-self.dpp); Rr=z[self.nv:].reshape(self.dpp,10); B=[]
        for a in range(2):
            M=np.zeros((5,5),complex); M[3]=self.bU[a]; B.append(M)
        for b in range(2):
            M=np.zeros((5,5),complex); M[4]=self.bV[b]; B.append(M)
        F3=np.concatenate([np.eye(self.dpp),V],1)@self.Pi
        for l in range(self.dpp):
            M=np.zeros((5,5),complex); M[:3]=F3[l].reshape(3,5); M[3:]=Rr[l].reshape(2,5); B.append(M)
        return np.array(B)
def dist(v,S):
    Q=np.linalg.qr(S.T)[0]; return np.linalg.norm(v-Q@(Q.conj().T@v))/max(1e-300,np.linalg.norm(v))
rng=np.random.default_rng(11)
G=rng.normal(size=(2,5))+1j*rng.normal(size=(2,5)); U=G-G.mean(1)[:,None]
V=np.linalg.svd(np.concatenate([U,np.ones((1,5))]))[2][3:].conj()
H=np.array([u*v for u in U for v in V]); print('generic U: singular values of U o U\':',np.array2string(np.linalg.svd(H,compute_uv=False),precision=2),' |U.V^T| %.0e'%np.abs(U@V.T).max())
t0=time.time()
for dpp,ns in ((1,6),(2,10),(3,10)):
    found=0; worst=[0,0,0]; res=[]
    for s in range(ns):
        P=SplitFixed(U,V,dpp,seed=s); z,c=solve(P,iters=300); res.append(c)
        if c<1e-10:
            found+=1; B=P.basis(z)
            for _ in range(3):
                co=rng.normal(size=dpp)+1j*rng.normal(size=dpp); Y=np.einsum('k,kab->ab',co,B[4:]); Y3=Y[:3]
                worst[0]=max(worst[0],np.abs(Y3.sum(0)).max()/np.abs(Y3).max())                       # column sums of 3-row part
                worst[1]=max(worst[1],dist(Y[3],U),dist(Y[4],V))                                         # lifts in U, U'
                X=1+Y3; Cv=np.array([sum(perm(X[:,[c for c in range(5) if c not in (j,k)]]) for k in range(5) if k!=j) for j in range(5)])
                worst[2]=max(worst[2],np.abs(Cv-24).max())                                              # strongly level
    print('fixed generic U, %d extra vectors (dim %d): found %d of %d; smallest res %s | on solutions: max |col sums| %.1e, lifts outside U,U\' %.1e, |C\'\'-24| %.1e ; t=%.0f'%(dpp,4+dpp,found,ns,np.array2string(np.sort(res)[:3],precision=1),worst[0],worst[1],worst[2],time.time()-t0),flush=True)
