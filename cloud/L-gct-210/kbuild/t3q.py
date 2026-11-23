import sys; sys.path.insert(0,'.')
from second import *
dE,Nb,Fs=setup([np.outer(u,chi(1))])
for m in (8,7,6):
    for s in (0,1):
        r,Z=iso(Fs,m,s,nfev=1200); print('T3 u chi1^T: m=%d seed %d res %.1e'%(m,s,r),flush=True)
        if r<1e-9: break
