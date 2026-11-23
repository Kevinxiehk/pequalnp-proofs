import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from math import comb
from level import Pk_grad, dc_basis
from tst import V, vk
def tangent(B, ks, seed=0, tol=1e-8):
    B=np.array(B,dtype=complex); B/=np.abs(B).max(); d=len(B); A=dc_basis(5)
    rng=np.random.default_rng(seed); R=comb(d+max(ks)-1,max(ks))+20
    xs=rng.normal(size=(R,d))+1j*rng.normal(size=(R,d))
    T=np.einsum('ri,iab->rab',xs,B); P,G=Pk_grad(T)
    GA=np.einsum('rkab,pab->rkp',G[:,ks],A)   # R,K,16 : DP_k(t) . A_p
    # unknown phi_{i,p}: phi(b_i) = sum_p phi_ip A_p ; condition sum_i x_i sum_p phi_ip GA[r,k,p] = 0
    M=np.einsum('ri,rkp->rkip',xs,GA).reshape(-1,d*16)
    s=np.linalg.svd(M,compute_uv=False); rk=int((s>tol*s[0]).sum())
    return d*16-rk-d*d
if __name__=='__main__':
    v=vk(1)
    print('tangent dim of {4-dim P234 spaces} at Vxv:', tangent([np.outer(a,v) for a in V],[2,3,4]))
    print('tangent dim of {4-dim p2p3 spaces} at Vxv:', tangent([np.outer(a,v) for a in V],[2,3]))
    print('tangent dim of {3-dim level} at Wxv:', tangent([np.outer(a,v) for a in V[:3]],[2,3,4,5]))
    for f in sys.argv[1:]:
        Tb=np.load(f); print(f, 'P234 tangent', tangent(Tb,[2,3,4]), 'p23 tangent', tangent(Tb,[2,3]))
