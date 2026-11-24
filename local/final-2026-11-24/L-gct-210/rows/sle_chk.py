# strongly level LINES C h (4x5): number of nonzero columns vs row-sum vector; usage: d s0 s1 tmax   (d = 1 or 2)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, time, collections
from clm import *
def rk(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum()) if s.size else 0
d,s0,s1=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]); tmax=float(sys.argv[4]); t0=time.time(); tab=collections.Counter(); ntry=0; ex={}
for s in range(s0,s1):
    if time.time()-t0>tmax: break
    P=Problem(4,d,'defect',0,seed=s); z,c=solve(P,iters=300); ntry+=1
    Z=P.basis(z)
    if c<1e-10 and np.linalg.cond(Z.reshape(d,-1))<1e6:
        Z=Z/np.abs(Z).max()
        q=rk(Z.sum(2)); ncol=sum(rk(Z[:,:,j])>0 for j in range(5)); colrk=tuple(sorted([rk(Z[:,:,j]) for j in range(5)],reverse=True))
        key=(q,ncol,colrk); tab[key]+=1; ex.setdefault(key,s)
        np.save('sle_d%d_s%d.npy'%(d,s),Z)
print('strongly level spaces of dim %d: found %d of %d'%(d,sum(tab.values()),ntry))
print('(row-sum rank, #nonzero columns, column ranks): count [first seed]')
for k in sorted(tab): print('  ',k,':',tab[k],'[seed %d]'%ex[k])
