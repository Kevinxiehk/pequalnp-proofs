import sys, time; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from math import comb
from level import Pk, Pk_grad
from srch import residuals
from blocksrch import ambient, run as brun
A25=np.zeros((25,5,5))
for i in range(5):
    for j in range(5): A25[i*5+j,i,j]=1
def extspace(B, ks=(1,2,3,4,5), R=300, seed=0, tol=1e-8):
    d=len(B); rng=np.random.default_rng(seed); xs=rng.normal(size=(R,d))+1j*rng.normal(size=(R,d))
    T=np.einsum('ri,iab->rab',xs,B); P,G=Pk_grad(T); rows=G[:,list(ks)].reshape(-1,25)
    u,s,vh=np.linalg.svd(rows); rk=int((s>tol*s[0]).sum()); return vh[rk:].conj()
def lm(init, d, ks, eps, seed, tl, maxit=400):
    rng=np.random.default_rng(seed); m=25; nsamp=comb(d+max(ks)-1,max(ks))+10
    C=np.array(init).reshape(len(init),25)
    Z=np.vstack([C, rng.normal(size=(m-len(C),m))+1j*rng.normal(size=(m-len(C),m))])
    Q,_=np.linalg.qr(Z.T); Q=Q.T
    X=eps*(rng.normal(size=(d,m-d))+1j*rng.normal(size=(d,m-d)))
    xs=rng.normal(size=(nsamp,d))+1j*rng.normal(size=(nsamp,d)); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
    lam=1e-3; r,J=residuals(X,Q,A25,xs,d,ks); f=np.linalg.norm(r); t0=time.time()
    for it in range(maxit):
        if time.time()-t0>tl: break
        JH=J.conj().T; H=JH@J; g=JH@r
        st=np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g); Xn=X+st.reshape(X.shape)
        rn=residuals(Xn,Q,A25,xs,d,ks,jac=False); fn=np.linalg.norm(rn)
        if fn<f: X=Xn; lam=max(lam/3,1e-12); r,J=residuals(X,Q,A25,xs,d,ks); f=fn
        else:
            lam*=4
            if lam>1e8: break
        if f<1e-12: break
    B=np.hstack([np.eye(d),X])@Q
    return f, np.einsum('iq,qab->iab',B,A25)
if __name__=='__main__':
    d=int(sys.argv[1]); seed=int(sys.argv[2]); starts=int(sys.argv[3])
    rng=np.random.default_rng(seed)
    f,T,_=brun(ambient([0,1,2]),4,[2,3],15,seed,25)
    T=T/np.abs(T).max(); E=extspace(T); print('base res %.1e'%f,'ext dim',len(E))
    best=None
    for s in range(starts):
        extra=(rng.normal(size=(d-4,len(E)))+1j*rng.normal(size=(d-4,len(E))))@E.reshape(len(E),25)
        init=list(T.reshape(4,25))+list(extra)
        fr,B=lm(init,d,[1,2,3,4,5],0.02,seed*100+s,float(sys.argv[4]))
        print(' start',s,'res %.2e'%fr,flush=True)
        if best is None or fr<best[0]: best=(fr,B)
        if fr<1e-11: break
    np.save(f'fullseed_d{d}_s{seed}.npy',best[1]); print('best',best[0])
