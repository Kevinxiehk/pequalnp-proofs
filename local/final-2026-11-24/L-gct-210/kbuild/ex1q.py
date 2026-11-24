import sys; sys.path.insert(0,'.')
from second import *
e=np.eye(5)
dE,Nb,Fs=setup([np.outer(u,e[0]-e[1]),np.outer(ub,e[2]-e[3])])
for m in (7,):
    for s in (0,1,2):
        r,Z=iso(Fs,m,s,nfev=1500); print('ex1 DC part (d=2): m=%d seed %d res %.1e'%(m,s,r),flush=True)
        if r<1e-9: break
