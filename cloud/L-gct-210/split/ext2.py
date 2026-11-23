import sys, time; sys.path.insert(0,'.'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
from core import *
from math import comb
def ext_space(L0,nsamp=300,seed=0):
    rng=np.random.default_rng(seed); d=len(L0)
    T=np.einsum('ri,iab->rab',rnd((nsamp,d),rng),L0); P,G=level.Pk_grad(T)
    rows=G[:,1:].reshape(-1,25); nr=np.linalg.norm(rows,axis=1); rows=rows[nr>1e-9*nr.max()]; rows=rows/np.linalg.norm(rows,axis=1,keepdims=True)
    u,s,vh=np.linalg.svd(rows); r=int((s>1e-8*s[0]).sum())
    return vh[r:].conj()   # rows: basis of E (bilinear annihilator)
def complement(L0,E):
    # orthonormal basis of E modulo span(L0) (hermitian complement inside E)
    Lf=L0.reshape(len(L0),-1); Q,_=np.linalg.qr(Lf.T)
    Y=E-(E@Q.conj())@Q.T
    u,s,vh=np.linalg.svd(Y); r=int((s>1e-8*s[0]).sum()); return vh[:r]
def search(L0,e,starts=10,maxit=150,seed=0,tlimit=60,C=None,verbose=False):
    rng=np.random.default_rng(seed)
    if C is None: C=complement(L0,ext_space(L0))
    c=len(C); d0=len(L0); d=d0+e; Cm=C.reshape(c,5,5)
    if c<e: return np.inf,None,c
    nsamp=comb(d+4,5)+10; t0=time.time(); best=(np.inf,None)
    for s in range(starts):
        Qr,_=np.linalg.qr(rnd((c,c),rng)); Qr=Qr.T
        X=0.5*rnd((e,c-e),rng)
        xs=rnd((nsamp,d),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        Cq=np.einsum('pq,qab->pab',Qr[e:],Cm)
        def res(X,jac=True):
            Bn=np.einsum('iq,qab->iab',np.hstack([np.eye(e),X])@Qr,Cm)
            T=np.einsum('ri,iab->rab',xs,np.concatenate([L0,Bn]))
            if not jac: return Pk(T)[:,1:].reshape(-1)
            P,G=level.Pk_grad(T); GC=np.einsum('rkab,pab->rkp',G[:,1:],Cq)
            J=np.einsum('ri,rkp->rkip',xs[:,d0:],GC); R,K=GC.shape[:2]
            return P[:,1:].reshape(-1), J.reshape(R*K,-1)
        lam=1e-3; r,J=res(X); f=np.linalg.norm(r)
        for it in range(maxit):
            if time.time()-t0>tlimit: break
            H=J.conj().T@J; g=J.conj().T@r
            Xn=X+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g).reshape(X.shape)
            fn=np.linalg.norm(res(Xn,False))
            if fn<f: X=Xn; lam=max(lam/3,1e-12); r,J=res(X); f=fn
            else:
                lam*=4
                if lam>1e8: break
            if f<1e-12: break
        if verbose: print(f'  start {s}: res {f:.2e} max|X| {np.abs(X).max() if X.size else 0:.1f}',flush=True)
        if f<best[0]:
            Bn=np.einsum('iq,qab->iab',np.hstack([np.eye(e),X])@Qr,Cm); best=(f,np.concatenate([L0,Bn]))
        if f<1e-11 or time.time()-t0>tlimit: break
    return best[0],best[1],c
def fresh(L,seed=7):
    Lf=L.reshape(len(L),-1); Q,_=np.linalg.qr(Lf.T); B=Q.T.reshape(len(L),5,5)
    T=np.einsum('rk,kij->rij',rnd((100,len(L)),np.random.default_rng(seed)),B)
    return np.abs(Pk(T)[:,1:]).max()
