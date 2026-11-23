# fresh strongly level 3-dim 4x5 spaces (unseeded): row-sum rank and number of zero columns
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time
from clm import *
def rk(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum()) if s.size else 0
s0,s1,tmax=int(sys.argv[1]),int(sys.argv[2]),float(sys.argv[3]); t0=time.time(); tab={}; ntry=0
for s in range(s0,s1):
    if time.time()-t0>tmax: break
    P=Problem(4,3,'defect',0,seed=s); z,c=solve(P,iters=250); ntry+=1
    Z=P.basis(z)
    if c<1e-9 and np.linalg.cond(Z.reshape(3,-1))<1e6:
        q=rk(Z.sum(2)); colrk=tuple(sorted([rk(Z[:,:,j]) for j in range(5)],reverse=True)); rowrk=tuple(sorted([rk(Z[:,i,:]) for i in range(4)],reverse=True))
        key=(q,colrk,rowrk); tab[key]=tab.get(key,0)+1
        np.save('sl3_s%d.npy'%s,Z)
print('strongly level 3-spaces found: %d of %d starts'%(sum(tab.values()),ntry))
print('(row-sum rank q, column ranks, row ranks): count')
for k in sorted(tab): print('  ',k,':',tab[k])
