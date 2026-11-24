import sys; sys.path.insert(0,'.')
from core import *
rowvecs={0:[np.array([1,1,1,0,0.]),np.array([0,0,0,1,0.]),np.array([0,0,0,0,1.])],1:[u],2:[ub]}
def weights(N):
    out=[]
    for a in range(3):
      for k in range(5):
        B=np.array([np.outer(r,chi(k)).ravel() for r in rowvecs[a]]).T
        M=np.hstack([N,B]); s=np.linalg.svd(M,compute_uv=False); r=(s>1e-8).sum()
        inter=N.shape[1]+B.shape[1]-r
        if inter: out.append(((a,k),inter))
    return out
for drop in range(4):
    B=[Kb[k] for k in range(4) if k!=drop]; N=E_of(B,nsamp=30); print('drop',drop,'dim',N.shape[1],weights(N))
