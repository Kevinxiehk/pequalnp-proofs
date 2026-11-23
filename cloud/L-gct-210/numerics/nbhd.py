import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/numerics')
from core import *
from ext_in_E import ext_search
def maxrank(B,seed=3):
    rng=np.random.default_rng(seed); Q=orth(B)
    x=rng.normal(size=len(Q))+1j*rng.normal(size=len(Q)); t=np.einsum('i,iab->ab',x,Q)
    sv=np.linalg.svd(t,compute_uv=False); return int(np.sum(sv>1e-7*sv[0]))
def desc(B):
    inv=invariants(B); dE=ext_space(B)[0]
    return (inv['dim'],inv['r'],inv['d'],tuple(sorted((inv['ra'],inv['rb']))),dE,maxrank(B))
L=orth(L080()); Lt=orth(np.array([L080()[i].T[::-1,::-1] for i in range(7)]))
print('L080 desc (dim,r,d,{ra,rb},extdim,genrank):',desc(L),flush=True)
rng=np.random.default_rng(int(sys.argv[1])); codim=int(sys.argv[2]); e=int(sys.argv[3]); ntries=int(sys.argv[4])
found={}
for tr in range(ntries):
    # random subspace of L080 of dim 7-codim
    C=rng.normal(size=(7-codim,7))+1j*rng.normal(size=(7-codim,7))
    S=orth(np.einsum('ij,jab->iab',C,L))
    dE,na,res,(fc,B)=ext_search(S,e,starts=3,seed=tr,tlimit=25)
    msg=f'try {tr}: sub dim {len(S)} dimE(S)={dE} target {len(S)+e}: fresh '+' '.join('%.0e'%r for r in res)
    if fc<1e-10:
        d=desc(B); msg+=f' FOUND desc={d}'
        # is it L080 itself? compare spans
        sv=np.linalg.svd(np.vstack([orth(B).reshape(len(B),-1),L.reshape(7,-1)]),compute_uv=False)
        msg+=f' dim(span(B,L080))={np.sum(sv>1e-8)}'
        sv=np.linalg.svd(np.vstack([orth(B).reshape(len(B),-1),Lt.reshape(7,-1)]),compute_uv=False); msg+=f' dim(span(B,L080^T))={np.sum(sv>1e-8)}'
        np.save(f'nb_c{codim}_e{e}_{sys.argv[1]}_{tr}.npy',B)
    print(msg,flush=True)
