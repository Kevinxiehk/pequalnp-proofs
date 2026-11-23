# calibration: r = 7, R = V (+) H, H = {be_4 = 0} (L080 type) or generic hyperplane; impose P_k (ks)
import sys, time
sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases'); sys.path.insert(0,'/home/claude/work/L-gct-210/lowd')
import numpy as np, level
from d1lm import DCB, ROW, COL, rnd
from math import comb
ks=[int(c) for c in sys.argv[1]]; Ht=sys.argv[2]; starts=int(sys.argv[3]); seed=int(sys.argv[4]); tl=float(sys.argv[5])
rng=np.random.default_rng(seed); t0=time.time()
for s in range(starts):
    if Ht=='H0': N=np.array([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1]],complex)
    else: mu=rnd(4,rng); N=np.linalg.svd(mu[None,:])[2][1:].conj()
    R=[ROW[k] for k in range(4)]+[np.einsum('p,pab->ab',N[q],COL) for q in range(3)]
    m=7; npar=16*m; p=0.5*rnd(npar,rng)
    xs=rnd((comb(m+max(ks)-1,max(ks))+20,m),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
    def build(p):
        Y=p.reshape(m,16); return np.array([R[k]+np.einsum('q,qab->ab',Y[k],DCB) for k in range(m)])
    dB=np.zeros((npar,m,5,5),complex)
    for k in range(m):
        for q in range(16): dB[16*k+q,k]=DCB[q]
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
    print(f'r7 ks={ks} H={Ht} start {s}: res {f:.2e} it {it}',flush=True)
    if time.time()-t0>tl: break
