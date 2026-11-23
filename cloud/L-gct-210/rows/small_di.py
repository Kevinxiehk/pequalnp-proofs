import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/rows')
import numpy as np, time
from clm import *
def run(p,d,e,ns,tmax):
    t0=time.time(); nf=0; nt=0; res=[]
    for s in range(ns):
        if time.time()-t0>tmax: break
        P=Problem(p,d,'defect',e,seed=s); z,c=solve(P,iters=300); Z=P.basis(z); cond=np.linalg.cond(Z.reshape(d,-1)); nt+=1; res.append(c if cond<1e6 else 9e9)
        if c<1e-9 and cond<1e6: nf+=1; np.save('di_p%d_d%d_e%d_s%d.npy'%(p,d,e,s),Z)
    print('L\' %dx5, (d,e)=(%d,%d) -> %dx5 level of dim %d: found %d of %d; smallest res %s'%(p,d,e,p+1,d+4-e,nf,nt,np.array2string(np.sort(res)[:3],precision=1)),flush=True)
for (p,d,e) in [(2,1,0),(2,2,1),(2,3,2),(2,4,3),(2,2,0),(2,3,1),(2,4,2)]: run(p,d,e,16,6)
for (p,d,e) in [(3,2,0),(3,3,1),(3,4,2),(3,5,3),(3,3,0),(3,4,1),(3,5,2),(3,6,3)]: run(p,d,e,16,9)
