import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from level import Pk_grad, dc_basis
from blocksrch import ambient, run as brun
from ext import run as erun
def dcext(B, ks, R=300, seed=0, tol=1e-8):
    A=dc_basis(5); d=len(B); rng=np.random.default_rng(seed); xs=rng.normal(size=(R,d))+1j*rng.normal(size=(R,d))
    T=np.einsum('ri,iab->rab',xs,B); P,G=Pk_grad(T); rows=np.einsum('rkab,pab->rkp',G[:,ks],A).reshape(-1,16)
    u,s,vh=np.linalg.svd(rows); rk=int((s>tol*s[0]).sum()); N=vh[rk:].conj(); return np.einsum('kp,pab->kab',N,A)
seed=int(sys.argv[1]); d=int(sys.argv[2]); ks=[int(c) for c in sys.argv[3]]
f,T,_=brun(ambient([0,1,2]),4,[2,3],15,seed,25); T=T/np.abs(T).max()
E=dcext(T,ks); rng=np.random.default_rng(seed)
best=9
for s in range(int(sys.argv[4])):
    extra=np.einsum('rk,kab->rab',rng.normal(size=(d-4,len(E)))+1j*rng.normal(size=(d-4,len(E))),E)
    f,B=erun(list(T)+list(extra),d,ks,1,seed*10+s,40,eps=0.01)
    print(' start',s,'res %.2e'%f,flush=True); best=min(best,f)
    if f<1e-11: np.save(f'dc5level_d{d}_s{seed}.npy',B); break
print('best',best)
