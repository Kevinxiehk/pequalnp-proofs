import sys; sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from level import Pk_grad
def extdim_full(B, ks=(1,2,3,4,5), R=300, seed=0, tol=1e-8):
    B=np.array(B,dtype=complex); d=len(B); rng=np.random.default_rng(seed)
    xs=rng.normal(size=(R,d))+1j*rng.normal(size=(R,d))
    T=np.einsum('ri,iab->rab',xs,B/np.abs(B).max()); P,G=Pk_grad(T)
    rows=G[:,list(ks)].reshape(-1,25); s=np.linalg.svd(rows,compute_uv=False)
    rk=int((s>tol*s[0]).sum()); return 25-rk
if __name__=='__main__':
    B=np.load('level4_1111.npy')
    print('first-order ext dim of the 4-dim DC level space in full 5x5:',extdim_full(B))
    print('... within DC only (k=2..5):'); sys.path.insert(0,'.')
    from extdim import extdim; print(extdim(B,[2,3,4,5])[0])
