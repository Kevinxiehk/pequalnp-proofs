# general m-dim subspaces of entry-sum-zero 5x5 matrices with P_2 = P_3 = 0 (chart parametrization)
import sys, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/lowd')
import numpy as np, level
from d1lm import rnd
from math import comb
m=int(sys.argv[1]); ks=[int(c) for c in sys.argv[2]]; starts=int(sys.argv[3]); seed=int(sys.argv[4]); tl=float(sys.argv[5])
rng=np.random.default_rng(seed); t0=time.time()
E=np.zeros((24,25))
for k in range(24): E[k,k]=1; E[k,24]=-1
E=E.reshape(24,5,5).astype(complex)
for s in range(starts):
    Q,_=np.linalg.qr(rnd((24,24),rng)); Bas=np.einsum('ij,jab->iab',Q,E)  # random basis of the 24-dim space
    npar=m*(24-m); p=0.3*rnd(npar,rng)
    xs=rnd((comb(m+max(ks)-1,max(ks))+20,m),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
    def build(p):
        Z=p.reshape(m,24-m); return Bas[:m]+np.einsum('kq,qab->kab',Z,Bas[m:])
    dB=np.zeros((npar,m,5,5),complex)
    for k in range(m):
        for q in range(24-m): dB[(24-m)*k+q,k]=Bas[m+q]
    def res(p,jac=True):
        T=np.einsum('ri,iab->rab',xs,build(p))
        if not jac: return level.Pk(T)[:,ks].reshape(-1)
        P,G=level.Pk_grad(T); dT=np.einsum('ri,qiab->rqab',xs,dB)
        return P[:,ks].reshape(-1), np.einsum('rkab,rqab->rkq',G[:,ks],dT).reshape(-1,npar)
    lam=1e-3; r,J=res(p); f=np.linalg.norm(r)
    for it in range(300):
        if time.time()-t0>tl: break
        H=J.conj().T@J; gg=J.conj().T@r
        pn=p+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-6)+1e-14*np.eye(npar),-gg)
        fn=np.linalg.norm(res(pn,False))
        if fn<f: p=pn; lam=max(lam/3,1e-12); r,J=res(p); f=fn
        else:
            lam*=4
            if lam>1e8: break
        if f<1e-12: break
    B=build(p); sv=np.linalg.svd(B.reshape(m,-1),compute_uv=False)
    print(f'm={m} ks={ks} start {s}: res {f:.2e} it {it} basis sv min/max {sv.min():.3f}/{sv.max():.3f}',flush=True)
    np.save(f'p23gen_{m}_{sys.argv[2]}_{seed}_{s}.npy',B)
    if time.time()-t0>tl: break
