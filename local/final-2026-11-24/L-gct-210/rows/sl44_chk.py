# strongly level spaces of dim d with column 4 identically zero (so K = (Q|0), Q a 4x4 level space with all column deletions level):
# row-sum rank and number of nonzero columns.  usage: d s0 s1 tmax
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, time, collections
from clm import *
from q44_search import PZ
def rk(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum()) if s.size else 0
d,s0,s1=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]); tmax=float(sys.argv[4]); t0=time.time(); tab=collections.Counter(); ntry=0
for s in range(s0,s1):
    if time.time()-t0>tmax: break
    P=PZ(d,0,s); z,c=solve(P,iters=300); ntry+=1
    Z=P.basis(z)
    if c<1e-10 and np.linalg.cond(Z.reshape(d,-1))<1e6:
        Z=Z/np.abs(Z).max(); cn=np.abs(Z).max((0,1)); q=rk(Z.sum(2))
        tab[(q,int((cn>1e-3).sum()),tuple(sorted([rk(Z[:,:,j],1e-4) for j in range(5)],reverse=True)))]+=1
print('strongly level, column 4 zero, dim %d: found %d of %d'%(d,sum(tab.values()),ntry))
for k in sorted(tab): print('   (row-sum rank, #nonzero columns, column ranks) =',k,':',tab[k])
