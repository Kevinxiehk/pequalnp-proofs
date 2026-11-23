# (B1) via the plane of a minimal pair. By C4 (chief; verified), for a minimal pair (r,r') with a_r = a_r' = 1 the plane X = X_{rr'}
# (2-dim, supported on the other three rows) is level and ALL ten 3x3 subpermanents vanish identically on it.
# Sample such planes by LM (rows 2,3,4 of 5x5 matrices; rows 0,1 = r,r' are zero), classify them, and compute the FO2 bound on the
# dimension of a level space containing X.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
from collections import Counter
A=list(sys.argv); SEED=int(A[1]) if len(A)>1 else 1; NTR=int(A[2]) if len(A)>2 else 30
sys.argv=[A[0]]
exec(open('/home/claude/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(SEED)
P3=np.array(list(itertools.permutations(range(3)))); TRIPLES=list(itertools.combinations(range(5),3))
def theta(x):                                   # x: (n,3,5) -> (n,10) all 3x3 subpermanents
    return np.stack([x[:,:,list(T)][:,np.arange(3)[None,:],P3].prod(axis=2).sum(axis=1) for T in TRIPLES],axis=1)
def P2(x):
    s=x.sum(axis=2); g=np.einsum('nij,nkj->nik',x,x); return s[:,0]*s[:,1]+s[:,0]*s[:,2]+s[:,1]*s[:,2]-g[:,0,1]-g[:,0,2]-g[:,1,2]
C8=rg.normal(size=(8,2))+1j*rg.normal(size=(8,2))
def res(z):
    B=(z[:30]+1j*z[30:]).reshape(2,3,5); x=np.tensordot(C8,B,axes=1)
    r=np.concatenate([theta(x).ravel(),P2(x),B.sum(axis=(1,2))]); Gm=B.reshape(2,15).conj()@B.reshape(2,15).T
    return np.concatenate([r.real,r.imag,[Gm[0,0].real-1,Gm[1,1].real-1,Gm[0,1].real,Gm[0,1].imag]])
def rk(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol).sum())
cnt=Counter(); fresh=np.random.default_rng(77); ex={}
for trial in range(NTR):
    z=rg.normal(size=60); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=400)
    if np.linalg.norm(s.fun)>1e-10: cnt['no convergence']+=1; continue
    B=(s.x[:30]+1j*s.x[30:]).reshape(2,3,5); c=fresh.normal(size=(20,2))+1j*fresh.normal(size=(20,2)); x=np.tensordot(c,B,axes=1)
    if abs(theta(x)).max()>1e-8 or abs(P2(x)).max()>1e-8: cnt['spurious']+=1; continue
    rows=tuple(sorted(rk(B[:,i,:]) for i in range(3))); cols=tuple(sorted(rk(B[:,:,j]) for j in range(5)))
    X=np.zeros((2,5,5),complex); X[:,2:,:]=B; n,rho,bd=FO2(X,fresh)
    key=('row proj',rows,'col proj',cols,'dim T_1',n,'rank',rho,'FO2 bound',bd); cnt[key]+=1; ex.setdefault(key,B)
for k,v in sorted(cnt.items(),key=lambda kv:-kv[1]): print(v,k,flush=True)
np.save('/tmp/r6_planes_%d.npy'%SEED,np.array([ex[k] for k in ex]))
