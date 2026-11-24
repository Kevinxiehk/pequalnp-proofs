# Lemma C test: column-centred level Y = Cg + X_A (X_A = {al (x) 1 + Gamma al}), full P2..P5.
import sys, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/lowd')
import numpy as np, level
from d1lm import DCB, ROW, rnd
from math import comb
seed=int(sys.argv[1]); starts=int(sys.argv[2]); tl=float(sys.argv[3])
rng=np.random.default_rng(seed); t0=time.time()
for s in range(starts):
    x0=rnd(16,rng); x0/=np.linalg.norm(x0)
    Qz,_=np.linalg.qr(np.column_stack([x0.conj(),rnd((16,15),rng)])); Zb=Qz[:,1:].T
    npar=15+64; p=0.5*rnd(npar,rng); d=5
    xs=rnd((comb(d+4,5)+20,d),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
    def build(p):
        Y=p[15:].reshape(4,16)
        B=[np.einsum('m,mab->ab',x0+p[:15]@Zb,DCB)]+[ROW[k]+np.einsum('m,mab->ab',Y[k],DCB) for k in range(4)]
        return np.array(B)
    dB=np.zeros((npar,5,5,5),complex)
    for q in range(15): dB[q,0]=np.einsum('m,mab->ab',Zb[q],DCB)
    for k in range(4):
        for m in range(16): dB[15+16*k+m,k+1]=DCB[m]
    def res(p,jac=True):
        T=np.einsum('ri,iab->rab',xs,build(p))
        if not jac: return level.Pk(T)[:,2:].reshape(-1)
        P,G=level.Pk_grad(T); dT=np.einsum('ri,qiab->rqab',xs,dB)
        return P[:,2:].reshape(-1), np.einsum('rkab,rqab->rkq',G[:,2:],dT).reshape(-1,npar)
    lam=1e-3; r,J=res(p); f=np.linalg.norm(r)
    for it in range(400):
        if time.time()-t0>tl: break
        H=J.conj().T@J; gg=J.conj().T@r
        pn=p+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-6)+1e-14*np.eye(npar),-gg)
        fn=np.linalg.norm(res(pn,False))
        if fn<f: p=pn; lam=max(lam/3,1e-12); r,J=res(p); f=fn
        else:
            lam*=4
            if lam>1e8: break
        if f<1e-12: break
    B=build(p); np.set_printoptions(precision=3,suppress=True,linewidth=150)
    print(f'start {s}: res {f:.2e} it {it}'); print(' |g|=\n',np.abs(B[0]).round(3)); print(' sum_k |x_k| =\n',np.abs(B[1:]).sum(0).round(3),flush=True)
    np.save(f'ccg_{seed}_{s}.npy',B)
    if time.time()-t0>tl: break
