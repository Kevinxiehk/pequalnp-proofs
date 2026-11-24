import sys; sys.path.insert(0,'.')
from second import *
name=sys.argv[1]
if name=='T2': g=np.outer(u,chi(1)+0.7*chi(4))+np.outer(ub,(0.3+0.5j)*chi(2)-1.1*chi(3))
if name=='T4': g=np.outer(np.array([1,2.5,-0.5+1j,-3-1j,0]),chi(1))
dE,Nb,Fs=setup([g])
for m in (8,7):
    for s in (0,1,2):
        r,Z=iso(Fs,m,s,nfev=1200); print('%s: m=%d seed %d res %.1e'%(name,m,s,r),flush=True)
        if r<1e-9: break
