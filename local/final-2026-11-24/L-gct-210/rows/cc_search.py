# (CC) search: column-centred 4x5 level spaces of dim d. usage: d s0 s1 tmax
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
import numpy as np, time
from clm import *
d=int(sys.argv[1]); s0=int(sys.argv[2]); s1=int(sys.argv[3]); tmax=float(sys.argv[4])
Rc=np.zeros((5,32))
for j in range(5): Rc[j,1<<j]=1
t0=time.time(); nf=0; ntry=0; res=[]
for s in range(s0,s1):
    if time.time()-t0>tmax: break
    P=Problem(4,d,'level',0,seed=s)
    P.R=np.concatenate([Rlevel(4),Rc],0)
    z,c=solve(P,iters=250); ntry+=1; res.append(c)
    Z=P.basis(z); cond=np.linalg.cond(Z.reshape(d,-1))
    if c<1e-9 and cond<1e6:
        nf+=1; sv=defect_dim(Z)
        print('d=%d seed %d res %.1e cond %.1e colsum %.1e defect sv %s'%(d,s,c,cond,abs(Z.sum(1)).max(),np.array2string(sv[:5],precision=2)),flush=True)
        np.save('cc_d%d_s%d.npy'%(d,s),Z)
print('(CC) d=%d: found %d of %d; smallest residuals %s; t=%.0f'%(d,nf,ntry,np.array2string(np.sort(res)[:4],precision=2),time.time()-t0))
