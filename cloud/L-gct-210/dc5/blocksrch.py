import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np, time
from math import comb
from srch import residuals
def ambient(rows):
    # matrices supported on given rows, all row & col sums zero
    idx=[(i,j) for i in rows for j in range(5)]; m=len(idx)
    C=[]
    for i in rows: C.append([1 if a==i else 0 for (a,b) in idx])
    for j in range(5): C.append([1 if b==j else 0 for (a,b) in idx])
    C=np.array(C,float); u,s,vh=np.linalg.svd(C); r=int((s>1e-9).sum()); N=vh[r:]
    A=np.zeros((len(N),5,5))
    for k,v in enumerate(N):
        for (a,b),x in zip(idx,v): A[k,a,b]=x
    return A
def run(A,d,ks,starts,seed,tl):
    rng=np.random.default_rng(seed); m=len(A); nsamp=comb(d+max(ks)-1,max(ks))+10; t0=time.time(); best=None
    for s in range(starts):
        Z=rng.normal(size=(m,m))+1j*rng.normal(size=(m,m)); Q=np.linalg.qr(Z)[0].T
        X=0.5*(rng.normal(size=(d,m-d))+1j*rng.normal(size=(d,m-d)))
        xs=rng.normal(size=(nsamp,d))+1j*rng.normal(size=(nsamp,d)); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        lam=1e-3; r,J=residuals(X,Q,A,xs,d,ks); f=np.linalg.norm(r)
        for it in range(300):
            JH=J.conj().T; H=JH@J; g=JH@r
            st=np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g); Xn=X+st.reshape(X.shape)
            rn=residuals(Xn,Q,A,xs,d,ks,jac=False); fn=np.linalg.norm(rn)
            if fn<f: X=Xn; lam=max(lam/3,1e-12); r,J=residuals(X,Q,A,xs,d,ks); f=fn
            else:
                lam*=4
                if lam>1e8: break
            if f<1e-12: break
        if best is None or f<best[0]: best=(f,X,Q)
        if f<1e-11 or time.time()-t0>tl: break
    f,X,Q=best; B=np.hstack([np.eye(d),X])@Q
    return f,np.einsum('iq,qab->iab',B,A),s+1
if __name__=='__main__':
    rows=[int(c) for c in sys.argv[1]]; d=int(sys.argv[2]); ks=[int(c) for c in sys.argv[3]]
    A=ambient(rows); f,T,ns=run(A,d,ks,int(sys.argv[4]),int(sys.argv[5]),float(sys.argv[6]))
    print('rows',rows,'ambient',len(A),'d',d,'ks',ks,'best res %.2e'%f,'starts used',ns)
    np.save(f'blk_{sys.argv[1]}_d{d}.npy',T)
