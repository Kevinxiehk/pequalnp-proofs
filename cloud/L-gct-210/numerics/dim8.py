import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/numerics')
from core import *
from ext_in_E import ext_search
import glob
def angle(B,C):
    Qb=orth(B).reshape(len(B),-1); Qc=orth(C).reshape(len(C),-1)
    s=np.linalg.svd(Qb.conj()@Qc.T,compute_uv=False); return np.sqrt(max(0,1-min(s)**2))
L=orth(L080())
for f in sorted(glob.glob('nb_*.npy')): print(f,'sin(max angle to L080)=%.1e'%angle(np.load(f),L))
rng=np.random.default_rng(7)
# 8-dim containing a k-dim subspace of L080, inside E(S)
for k in [6,5,4]:
  for tr in range(2):
    C=rng.normal(size=(k,7))+1j*rng.normal(size=(k,7)); S=orth(np.einsum('ij,jab->iab',C,L))
    dE,E,_=ext_space(S)
    if dE==8 and k==6:
        print(f'k=6: E(S) is 8-dim; fresh check of E(S) itself: {fresh_check(E):.2e}',flush=True); continue
    dE,na,res,(fc,B)=ext_search(S,8-k,starts=2,seed=tr,tlimit=25)
    print(f'k={k}: dimE(S)={dE} 8-dim search fresh:',['%.1e'%r for r in res],flush=True)
    if fc<1e-10: np.save(f'D8_k{k}_{tr}.npy',B); print('  FOUND',report('8',B))
