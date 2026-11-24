# LM: L = D (d-dim DC, free) + lift of a FIXED r-dim R in V(+)V (basis Rb: r x 8 coords in F-basis),
# impose P_k, k in ks.  usage: rdlm.py ks d Rtype starts seed tlimit ; Rtype: gen7 | VH (V + generic hyperplane) | VH0 (V + {be_4=0})
import sys, time
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/lowd')
import numpy as np, level
from d1lm import DCB, ROW, COL, rnd
from math import comb
ks=[int(c) for c in sys.argv[1]]; d=int(sys.argv[2]); Rtype=sys.argv[3]
starts=int(sys.argv[4]); seed=int(sys.argv[5]); tl=float(sys.argv[6])
rng=np.random.default_rng(seed); t0=time.time()
AB=np.concatenate([ROW,COL])  # 8 x 5 x 5 (alpha=f_p, beta=f_p)
for s in range(starts):
    if Rtype=='gen7': Rb=rnd((7,8),rng)
    elif Rtype=='VH': mu=rnd(4,rng); N=np.linalg.svd(mu[None,:])[2][1:].conj(); Rb=np.zeros((7,8),complex); Rb[:4,:4]=np.eye(4); Rb[4:,4:]=N
    elif Rtype=='VH0':
        # beta in {beta_4=0}: beta = sum c_p f_p with f_p = e_p - e_4 ; beta_4 = -sum c_p = 0
        N=np.array([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1]],complex); Rb=np.zeros((7,8),complex); Rb[:4,:4]=np.eye(4); Rb[4:,4:]=N
    elif Rtype=='ex1':
        Rb=np.zeros((5,8),complex); Rb[0,:4]=[1,1,1,0]; Rb[1:,4:]=np.eye(4)
    elif Rtype=='VH0r6':
        N=np.array([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1]],complex); Rb=np.zeros((6,8),complex); Rb[:3,:4]=N; Rb[3:,4:]=N
    r=len(Rb); m=d+r
    Rmat=np.einsum('rp,pab->rab',Rb,AB)
    G0=rnd((d,16),rng); Qz,_=np.linalg.qr(np.column_stack([G0.conj().T,rnd((16,16-d),rng)])); Zb=Qz[:,d:].T
    npar=(16-d)*d+16*r; p=0.5*rnd(npar,rng)
    xs=rnd((comb(m+max(ks)-1,max(ks))+20,m),rng); xs/=np.linalg.norm(xs,axis=1,keepdims=True)
    def build(p):
        Dp=G0+p[:(16-d)*d].reshape(d,16-d)@Zb; Y=p[(16-d)*d:].reshape(r,16)
        B=[np.einsum('m,mab->ab',Dp[k],DCB) for k in range(d)]+[Rmat[k]+np.einsum('m,mab->ab',Y[k],DCB) for k in range(r)]
        return np.array(B)
    dB=np.zeros((npar,m,5,5),complex)
    for k in range(d):
        for q in range(16-d): dB[(16-d)*k+q,k]=np.einsum('m,mab->ab',Zb[q],DCB)
    for k in range(r):
        for q in range(16): dB[(16-d)*d+16*k+q,d+k]=DCB[q]
    def res(p,jac=True):
        T=np.einsum('ri,iab->rab',xs,build(p))
        if not jac: return level.Pk(T)[:,ks].reshape(-1)
        P,G=level.Pk_grad(T); dT=np.einsum('ri,qiab->rqab',xs,dB)
        return P[:,ks].reshape(-1), np.einsum('rkab,rqab->rkq',G[:,ks],dT).reshape(-1,npar)
    lam=1e-3; rr,J=res(p); f=np.linalg.norm(rr)
    for it in range(300):
        if time.time()-t0>tl: break
        H=J.conj().T@J; gg=J.conj().T@rr
        pn=p+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-6)+1e-14*np.eye(npar),-gg)
        fn=np.linalg.norm(res(pn,False))
        if fn<f: p=pn; lam=max(lam/3,1e-12); rr,J=res(p); f=fn
        else:
            lam*=4
            if lam>1e8: break
        if f<1e-12: break
    B=build(p); sv=np.linalg.svd(B[:d].reshape(d,-1),compute_uv=False)
    print(f'ks={ks} d={d} R={Rtype} start {s}: res {f:.2e} it {it} DC sv {sv.round(3)}',flush=True)
    np.save(f'rd_{sys.argv[1]}_{d}_{Rtype}_{seed}_{s}.npy',B)
    if time.time()-t0>tl: break
