import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/numerics')
from core import *
from ext_in_E import ext_search
def angle(B,C):
    Qb=orth(B).reshape(len(B),-1); Qc=orth(C).reshape(len(C),-1)
    s=np.linalg.svd(Qb.conj()@Qc.T,compute_uv=False); return np.sqrt(max(0,1-min(s)**2))
L=orth(L080()); rng=np.random.default_rng(3)
for k in [4,3]:
    C=rng.normal(size=(k,7))+1j*rng.normal(size=(k,7)); S=orth(np.einsum('ij,jab->iab',C,L))
    dE,na,res,(fc,B)=ext_search(S,7-k,starts=2,seed=k,tlimit=20)
    print(f'recover L080 from generic {k}-dim subspace: dimE(S)={dE} fresh',['%.0e'%r for r in res], 'angle to L080 %.1e'%angle(B,L) if fc<1e-10 else '',flush=True)
# W5+1 sanity in 4-dim and also D=5 from the found 4-dim (r,d)=(1,3) space
