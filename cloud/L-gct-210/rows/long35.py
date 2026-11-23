import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time
from clm import *
from rect import describe
t0=time.time()
for s in (0,7,1,4):
    if time.time()-t0>130: break
    P=Problem(3,5,'level',0,seed=s); z,c=solve(P,iters=250)
    for rep in range(6):
        z,c=solve(P,z0=z,iters=400)
        if c<1e-11 or time.time()-t0>150: break
    Z=P.basis(z)
    print('seed',s,'res %.2e'%c,'t=%.0f'%(time.time()-t0),flush=True)
    u_,s_,vh_=np.linalg.svd(Z.reshape(5,-1),full_matrices=False); Zo=vh_.reshape(5,3,5)
    # singular values of projection off each row (free-row detection, soft)
    for i in range(3):
        sv=np.linalg.svd(np.delete(Zo,i,axis=1).reshape(5,-1),compute_uv=False)
        print('   off-row',i,'sv',np.array2string(sv,precision=1),flush=True)
    for j in range(5):
        sv=np.linalg.svd(np.delete(Zo,j,axis=2).reshape(5,-1),compute_uv=False)
        print('   off-col',j,'sv',np.array2string(sv,precision=1),flush=True)
    np.save('long35_s%d.npy'%s,Z)
