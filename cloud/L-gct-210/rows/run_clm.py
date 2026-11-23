import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time
from clm import *
from rect import describe
p=int(sys.argv[1]); d=int(sys.argv[2]); mode=sys.argv[3]; e=int(sys.argv[4]); s0=int(sys.argv[5]); s1=int(sys.argv[6])
tmax=float(sys.argv[7]) if len(sys.argv)>7 else 150
t0=time.time(); nf=0
for s in range(s0,s1):
    if time.time()-t0>tmax: print('time limit'); break
    P=Problem(p,d,mode,e,seed=s); z,c=solve(P,iters=250)
    Z=P.basis(z); cond=np.linalg.cond(Z.reshape(d,-1))
    line='p=%d d=%d %s e=%d seed %d res %.2e cond %.1e t=%.0f'%(p,d,mode,e,s,c,cond,time.time()-t0)
    if c<1e-9 and cond<1e6:
        nf+=1
        if p==4: line+=' defect sv '+np.array2string(defect_dim(Z)[:5],precision=2)
        print(line,flush=True); print('    ',describe(Z),flush=True)
        np.save('clm_p%d_d%d_%s%d_s%d.npy'%(p,d,mode,e,s),Z)
    else: print(line,flush=True)
print('found',nf)
