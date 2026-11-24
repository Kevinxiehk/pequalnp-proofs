import numpy as np, sys
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2')
import vlib, fo2lib
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
S=vlib.spaces()
for name,B in S.items():
    B=np.asarray(B,dtype=complex); d=len(B)
    if B.shape[1:]!=(5,5): print(name,'skipped (shape',B.shape,')'); continue
    dT,r,bd,inT,iso,sg=fo2lib.fo2(B,rng)
    # random subspace of codimension 2
    Mc=rng.normal(size=(d-2,d))
    dT2,r2,bd2,_,_,_=fo2lib.fo2(B,rng,M=Mc)
    print('%-14s dim %d | M = L: dim T_1 = %2d, rank = %d, bound = %d (L in T_1: %.1e, isotropic: %.1e; sv gap %.1e/%.1e) | M codim 2: dim T_1 = %2d, rank = %d, bound = %d'%(
        name,d,dT,r,bd,inT,iso,sg[r-1] if r>0 else 0,sg[r] if r<len(sg) else 0,dT2,r2,bd2),flush=True)
