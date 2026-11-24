"""seeded LM: start near span(init basis + random extra rows)."""
import sys, time
sys.path.insert(0, '/home/kevxhk/work/L-gct-086/smallcases'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5')
import numpy as np
from math import comb
from level import Pk, dc_basis
from srch import residuals
def run(init, d, ks, starts, seed, tlimit, eps=0.3, maxit=300):
    rng=np.random.default_rng(seed); A=dc_basis(5); m=16
    C0=np.array([t[:4,:4].ravel() for t in init])  # coords
    t0=time.time(); best=None
    nsamp=comb(d+max(ks)-1,max(ks))+10
    for s in range(starts):
        extra=rng.normal(size=(d-len(C0),m))+1j*rng.normal(size=(d-len(C0),m))
        C=np.vstack([C0,extra]) if d>len(C0) else C0
        Z=np.vstack([C, rng.normal(size=(m-d,m))+1j*rng.normal(size=(m-d,m))])
        Q,_=np.linalg.qr(Z.T); Q=Q.T   # first d rows span C (Gram-Schmidt)
        X=eps*(rng.normal(size=(d,m-d))+1j*rng.normal(size=(d,m-d)))
        xs=rng.normal(size=(nsamp,d))+1j*rng.normal(size=(nsamp,d)); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
        lam=1e-3; r,J=residuals(X,Q,A,xs,d,ks); f=np.linalg.norm(r)
        for it in range(maxit):
            if time.time()-t0>tlimit: break
            JH=J.conj().T; H=JH@J; g=JH@r
            step=np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-12),-g)
            Xn=X+step.reshape(X.shape); rn=residuals(Xn,Q,A,xs,d,ks,jac=False); fn=np.linalg.norm(rn)
            if fn<f: X=Xn; lam=max(lam/3,1e-12); r,J=residuals(X,Q,A,xs,d,ks); f=fn
            else:
                lam*=4
                if lam>1e8: break
            if f<1e-12: break
        print(f'start {s}: res {f:.3e} |X| {np.linalg.norm(X):.2e} it {it}',flush=True)
        if best is None or f<best[0]: best=(f,X.copy(),Q.copy())
        if f<1e-11 or time.time()-t0>tlimit: break
    f,X,Q=best; B=np.hstack([np.eye(d),X])@Q
    return f,np.einsum('iq,qab->iab',B,A)
if __name__=='__main__':
    from tst import V, vk
    d=int(sys.argv[1]); ks=[int(c) for c in sys.argv[2]]; eps=float(sys.argv[3]); starts=int(sys.argv[4]); seed=int(sys.argv[5])
    init=[np.outer(a,vk(1)) for a in V]
    f,Tb=run(init,d,ks,starts,seed,100,eps)
    print('final',f); np.save(f'ext_d{d}_k{sys.argv[2]}_e{eps}_s{seed}.npy',Tb)
