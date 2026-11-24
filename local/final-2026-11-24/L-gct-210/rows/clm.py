"""Holomorphic complex LM on Grassmannian charts for p x 5 problems:
 mode 'level'  : P_1..P_p = 0
 mode 'deg'    : p=4, P_1..P_3 = 0 and all five max-minor permanents = 0   (degenerate level)
 mode 'defect' : p=4, deletion vectors p_k(Y)_j = P_k(Y^(j)) (k=1..4) lie in an unknown e-dim subspace of 1^perp
                 (e=0: strongly level).  This implies 4x5 level.
"""
import sys, time
import numpy as np
Q=5
SUB=[np.array([S for S in range(32) if not (S>>j)&1]) for j in range(Q)]
DEG=np.array([bin(S).count('1') for S in range(32)])
def shiftj(G,j):
    out=np.zeros_like(G); out[:,SUB[j]|(1<<j)]=G[:,SUB[j]]; return out
def mul1p(G,l):
    out=G.copy()
    for j in range(Q): out[:,SUB[j]|(1<<j)]+=l[:,j][:,None]*G[:,SUB[j]]
    return out
def G_and_loo(X):
    N,p,_=X.shape
    one=np.zeros((N,32),complex); one[:,0]=1
    pre=[one]
    for i in range(p): pre.append(mul1p(pre[-1],X[:,i]))
    suf=[one]
    for i in range(p-1,-1,-1): suf.append(mul1p(suf[-1],X[:,i]))
    suf=suf[::-1]   # suf[i] = prod_{k>=i}
    loo=[]
    for i in range(p):
        g=pre[i]
        for k in range(i+1,p): g=mul1p(g,X[:,k])
        loo.append(g)
    return pre[p],loo
def Rlevel(p):
    R=np.zeros((p,32)); 
    for k in range(1,p+1): R[k-1,DEG==k]=1
    return R
def Rdeg():
    R=np.zeros((8,32))
    for k in range(1,4): R[k-1,DEG==k]=1
    for j in range(Q): R[3+j,31^(1<<j)]=1
    return R
def Rdel():
    """(4,5,32): p_k[j] = sum_{|T|=k, j not in T} G[T]"""
    R=np.zeros((4,5,32))
    for k in range(1,5):
        for j in range(Q):
            for S in range(32):
                if DEG[S]==k and not (S>>j)&1: R[k-1,j,S]=1
    return R
class Problem:
    def __init__(self,p,d,mode,e=0,seed=0,N=None):
        self.p,self.d,self.mode,self.e=p,d,mode,e
        rng=np.random.default_rng(seed); self.rng=rng
        n=p*Q
        M=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)); self.Pi,_=np.linalg.qr(M)
        self.N=N or 140
        A=rng.normal(size=(self.N,d))+1j*rng.normal(size=(self.N,d)); self.A=A/np.linalg.norm(A,axis=1)[:,None]
        self.nW=d*(n-d)
        if mode=='level': self.R=Rlevel(p)
        elif mode=='deg': self.R=Rdeg()
        else:
            self.Rd=Rdel()
            # basis of 1^perp
            B=rng.normal(size=(4,5))+1j*rng.normal(size=(4,5)); B=B-B.mean(1)[:,None]
            q,_=np.linalg.qr(B.T); self.Fb=q.T          # rows f_i spanning 1^perp (4,5), orthonormal
            self.Fd=q.conj().T                           # coordinates c = Fd p  for p in 1^perp
            self.nT=e*(4-e)
        self.nvar=self.nW+(self.nT if mode=='defect' else 0)
    def Zfull(self,z):
        W=z[:self.nW].reshape(self.d,-1)
        return np.concatenate([np.eye(self.d),W],1)@self.Pi
    def basis(self,z): return self.Zfull(z).reshape(self.d,self.p,Q)
    def defect_space(self,z):
        T=z[self.nW:].reshape(self.e,4-self.e)
        return np.concatenate([np.eye(self.e),T],1)@self.Fb     # rows span the defect space
    def fun(self,z,jac=True):
        p,d,N=self.p,self.d,self.N; n=p*Q
        Zf=self.Zfull(z); X=(self.A@Zf).reshape(N,p,Q)
        G,loo=G_and_loo(X)
        # dG/dx_ij = shift_j(loo[i]) : (N,p,Q,32)
        if jac: dG=np.stack([np.stack([shiftj(loo[i],j) for j in range(Q)],1) for i in range(p)],1)
        if self.mode in ('level','deg'):
            r=G@self.R.T                                        # (N,nr)
            if not jac: return r.ravel()
            D=np.einsum('nijs,rs->nrij',dG,self.R).reshape(N,-1,n)   # (N,nr,n)
            Jt=None
        else:
            e=self.e; T=z[self.nW:].reshape(e,4-e)
            pk=np.einsum('ns,kjs->nkj',G,self.Rd)              # (N,4,5)
            c=np.einsum('nkj,ij->nki',pk,self.Fd)              # (N,4,4)
            sm=pk.sum(2)                                        # (N,4)
            r2=c[:,:,e:]-np.einsum('nka,ab->nkb',c[:,:,:e],T)   # (N,4,4-e)
            # weights to balance degrees
            r=np.concatenate([sm,r2.reshape(N,-1)],1)
            if not jac: return r.ravel()
            dpk=np.einsum('nijs,kms->nkmij',dG,self.Rd).reshape(N,4,5,n)
            dc=np.einsum('nkmx,im->nkix',dpk,self.Fd)
            dsm=dpk.sum(2)
            dr2=dc[:,:,e:,:]-np.einsum('nkax,ab->nkbx',dc[:,:,:e,:],T)
            D=np.concatenate([dsm,dr2.reshape(N,-1,n)],1)
            # jac wrt T: d r2[n,k,b]/dT[a,b'] = -delta_bb' c[n,k,a]
            Jt=np.zeros((N,4,4-e,e,4-e),complex)
            for b in range(4-e): Jt[:,:,b,:,b]=-c[:,:,:e]
            Jt=np.concatenate([np.zeros((N,4,e*(4-e)),complex),Jt.reshape(N,4*(4-e),e*(4-e))],1)
        nr=D.shape[1]
        DP=D@self.Pi[d:].T                                      # (N,nr,n-d)
        JW=np.einsum('na,nrb->nrab',self.A,DP).reshape(N*nr,self.nW)
        J=JW if Jt is None else np.concatenate([JW,Jt.reshape(N*nr,-1)],1)
        return r.ravel(),J
def solve(P,z0=None,iters=300,verbose=False,tol=1e-13):
    rng=P.rng
    z=z0 if z0 is not None else (rng.normal(size=P.nvar)+1j*rng.normal(size=P.nvar))*0.5
    mu=1e-2; r,J=P.fun(z); c=np.linalg.norm(r)
    for it in range(iters):
        H=J.conj().T@J; g=J.conj().T@r
        ok=False
        for _ in range(12):
            try: dz=-np.linalg.solve(H+mu*np.eye(len(H))*max(1e-30,np.trace(H).real/len(H)),g)
            except np.linalg.LinAlgError: mu*=10; continue
            rn=P.fun(z+dz,jac=False); cn=np.linalg.norm(rn)
            if cn<c: ok=True; break
            mu*=4
        if not ok: break
        z=z+dz; mu=max(mu/3,1e-12); r,J=P.fun(z); cprev,c=c,cn
        if verbose and it%20==0: print(it,c,mu)
        if c<tol: break
    return z,c
def fresh_level(Z,deg=False,seed=7,n=60):
    rng=np.random.default_rng(seed); d,p,_=Z.shape
    A=rng.normal(size=(n,d))+1j*rng.normal(size=(n,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    R=Rdeg() if deg else Rlevel(p); return np.abs(G@R.T).max()
def defect_dim(Z,seed=8,n=80,tol=1e-7):
    """4x5 space: singular values of the deletion-defect vectors p_k(Y), k=1..4"""
    rng=np.random.default_rng(seed); d,p,_=Z.shape
    A=rng.normal(size=(n,d))+1j*rng.normal(size=(n,d)); A/=np.linalg.norm(A,axis=1)[:,None]
    X=np.einsum('nk,kab->nab',A,Z); G,_=G_and_loo(X)
    pk=np.einsum('ns,kjs->nkj',G,Rdel()).reshape(-1,5)
    s=np.linalg.svd(pk,compute_uv=False); return s
