import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
ex=examples()
rng=np.random.default_rng(11)
for name,B in ex.items():
    D=dcpart(orth(B))
    if len(D)==0: continue
    D=orth(D)
    c=rng.normal(size=len(D))+1j*rng.normal(size=len(D)); dl=np.einsum('k,kij->ij',c,D)
    Hs={k:VB@hess_full(dl,k)@VB.T for k in (3,4,5)}
    print(name,'d=',len(D),'supp',int((abs(dl)>1e-9).sum()),'ranks H3,H4,H5 on V:',[rank(Hs[k]) for k in (3,4,5)],
          'rank of [H3;H4;H5]:',rank(np.vstack([Hs[3],Hs[4],Hs[5]])))
