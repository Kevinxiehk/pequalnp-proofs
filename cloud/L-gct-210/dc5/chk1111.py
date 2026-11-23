import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/dc5'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
import numpy as np
from graded import solve, build
from level import Pk
sols=solve([1,1,1,1],[2,3,4,5],8,1,tl=14)
good=[s for s in sols if s[0]<1e-9]
print('found',len(good))
np.set_printoptions(precision=4,suppress=True,linewidth=160)
for f,p,Qs in good:
    B=build(p,[1,1,1,1],Qs); print('rank',np.linalg.matrix_rank(B.reshape(4,25),1e-8))
    rng=np.random.default_rng(42); worst=0
    for _ in range(30):
        x=rng.normal(size=4)+1j*rng.normal(size=4); x/=np.linalg.norm(x)
        T=np.einsum('i,iab->ab',x,B/np.abs(B).max()); worst=max(worst,np.abs(Pk(T)[0][1:]).max())
    print('fresh-point max |P_k|',worst)
    for b in B:
        u,s,vh=np.linalg.svd(b); a=u[:,0]*s[0]; a=a/a[np.argmax(np.abs(a))]; print(' a =',np.round(a,4))
    np.save('level4_1111.npy',B)
