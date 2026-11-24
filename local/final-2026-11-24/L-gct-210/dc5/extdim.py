import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5')
import numpy as np
from level import Pk_grad, dc_basis
def extdim(B, ks, R=200, seed=0, tol=1e-8):
    B=np.array(B); d=len(B); rng=np.random.default_rng(seed); A=dc_basis(5)
    xs=rng.normal(size=(R,d))+1j*rng.normal(size=(R,d))
    T=np.einsum('ri,iab->rab',xs,B/np.abs(B).max())
    P,G=Pk_grad(T)
    rows=np.einsum('rkab,pab->rkp',G[:,ks],A).reshape(-1,16)
    s=np.linalg.svd(rows,compute_uv=False)
    rk=int((s>tol*s[0]).sum()); return 16-rk, s[max(rk-2,0):rk+2]
if __name__=='__main__':
    from tst import V, vk
    K=[np.outer(a,vk(1)) for a in V]
    for ks in ([2],[2,3],[2,3,4],[2,3,4,5]): print('V x v, ks',ks,'ext dim',extdim(K,ks))
    W=[I for I in K[:3]]
    for ks in ([2,3,4],[2,3,4,5]): print('W x v (w_5=0 rows), ks',ks,'ext dim',extdim(W,ks))
