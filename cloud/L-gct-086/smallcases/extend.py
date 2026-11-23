"""extend a fixed level space W (d0 x n x n) by e new directions (full ambient) via LM."""
import sys, time; sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
from tangent import *
from search import ambient
from math import comb
def extend(W,n,e,starts=10,maxit=200,seed=0,tlimit=80):
    rng=np.random.default_rng(seed); A=ambient(n,'full'); m=n*n; d0=len(W); d=d0+e
    nsamp=comb(d+n-1,n)+10; t0=time.time(); best=(np.inf,None)
    for s in range(starts):
        Z=rng.normal(size=(m,m))+1j*rng.normal(size=(m,m)); Q,_=np.linalg.qr(Z); Q=Q.T
        X=0.3*(rng.normal(size=(e,m-e))+1j*rng.normal(size=(e,m-e)))
        xs=rng.normal(size=(nsamp,d))+1j*rng.normal(size=(nsamp,d)); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        C=np.einsum('pq,qab->pab',Q[e:],A)
        def res(X,jac=True):
            Bn=np.einsum('iq,qab->iab',np.hstack([np.eye(e),X])@Q,A)
            T=np.einsum('ri,iab->rab',xs,np.concatenate([W,Bn]))
            if not jac: return Pk(T)[:,1:].reshape(-1)
            P,G=Pk_grad(T); GC=np.einsum('rkab,pab->rkp',G[:,1:],C)
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
        print(f' start {s}: res {f:.2e}',flush=True)
        if f<best[0]: best=(f,np.concatenate([W,np.einsum('iq,qab->iab',np.hstack([np.eye(e),X])@Q,A)]))
        if f<1e-11 or time.time()-t0>tlimit: break
    return best
if __name__=='__main__':
    which=sys.argv[1]; e=int(sys.argv[2])
    if which=='w4': n=4; W=weight_space(4,[1,2,3,0],[1,2,0,3],12,[1,2])
    if which=='w5': n=5; W=weight_space(5,[1,2,3,4,0],[1,2,0,4,3],30,[2,3,4])
    f,B=extend(W,n,e,starts=int(sys.argv[3]),seed=int(sys.argv[4]))
    print(which,'dim',len(W)+e,'res',f,'fresh check',check_numeric(B,n)[1:].max() if B is not None else None)
    np.save(f'ext_{which}_{e}.npy',B)
